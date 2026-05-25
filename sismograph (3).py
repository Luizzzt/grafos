# =============================================================================
# SismoGraph - Analise de Impacto Sismico na Asia por Teoria dos Grafos
# =============================================================================
# Integrantes:
#   Luiz Fernando Ferrari Batistela  - RA 10427397
#   Henrique Jeam Lima               - RA 10277156
#
# Disciplina : Teoria dos Grafos - Turma 6G
# Professor  : Prof. Dr. Ivan Carlos Alcantara de Oliveira
# Instituicao: Universidade Presbiteriana Mackenzie
#
# Descricao  : Aplicacao que modela a rede de impacto sismico na Asia como
#              um grafo nao orientado ponderado (Tipo 2). Os vertices
#              representam cidades asiaticas (IDs 0-39) e epicentros de
#              terremotos historicos (IDs 40-69). As arestas representam a
#              intensidade sismica percebida (escala MMI) entre cada par.
#
# Historico de alteracoes:
#   2026-02-12 | Luiz Fernando | Versao inicial (Parte 1): estrutura do grafo,
#              | I/O, insercao/remocao de vertices e arestas, exibicao.
#   2026-03-10 | Henrique Jeam | Parte 2: analise de conexidade (BFS/Kosaraju),
#              | grafo reduzido, correcao de bugs no parser de arquivo.
#   2026-05-23 | Luiz Fernando | Parte 3: Dijkstra (caminho de maior
#              | intensidade sismica), grau dos vertices, verificacao
#              | euleriana, verificacao hamiltoniana, arvore geradora minima
#              | (Kruskal).
# =============================================================================

import os
import math
from collections import defaultdict, deque
import heapq

# =============================================================================
# CLASSE GRAFO
# =============================================================================

class Grafo:
    """
    Representa um grafo por lista de adjacencia.

    Atributos:
        tipo       (int)  : tipo do grafo conforme convencao da disciplina (0-7)
        vertices   (dict) : {id -> {'rotulo': str, 'peso': str}}
        adj        (defaultdict): {id -> [(vizinho, peso_aresta), ...]}
    """

    def __init__(self):
        self.tipo = 2          # Nao orientado com peso nas arestas
        self.vertices = {}
        self.adj = defaultdict(list)

    # ------------------------------------------------------------------
    # Utilitarios internos
    # ------------------------------------------------------------------

    def _eh_nao_orientado(self):
        """Retorna True se o tipo do grafo indica nao orientado (tipos 0-3)."""
        return self.tipo in (0, 1, 2, 3)

    def _eh_ponderado(self):
        """Retorna True se o tipo indica peso nas arestas (tipos 2,3,6,7)."""
        return self.tipo in (2, 3, 6, 7)

    def _aresta_existe(self, u, v):
        """Verifica se a aresta (u,v) ja existe na lista de adjacencia."""
        return any(viz == v for viz, _ in self.adj[u])

    def _contar_arestas(self):
        """Conta o numero de arestas (sem duplicar para grafos nao orientados)."""
        total = sum(len(vizinhos) for vizinhos in self.adj.values())
        if self._eh_nao_orientado():
            total //= 2
        return total

    def _tipo_vertice(self, vid):
        """Classifica o vertice como Cidade (0-39) ou Epicentro (40-69)."""
        return "Cidade" if vid <= 39 else "Epicentro"

    # ------------------------------------------------------------------
    # I/O - Leitura e gravacao do arquivo grafo.txt
    # ------------------------------------------------------------------

    def ler_arquivo(self, caminho):
        """
        Le o grafo de um arquivo texto no formato padrao da disciplina.
        Formato:
            Linha 1     : tipo do grafo
            Linha 2     : numero de vertices (n)
            Linhas 3..  : ID "Rotulo" "Peso"   (n linhas)
            Linha n+3   : numero de arestas (m)
            Linhas n+4..: ID_u ID_v Peso        (m linhas)
        """
        try:
            with open(caminho, 'r', encoding='utf-8') as f:
                linhas = [l.strip() for l in f if l.strip()]

            idx = 0
            self.tipo = int(linhas[idx]); idx += 1
            n = int(linhas[idx]); idx += 1

            self.vertices = {}
            self.adj = defaultdict(list)

            for _ in range(n):
                partes = linhas[idx].split('"')
                vid = int(partes[0].strip())
                rotulo = partes[1]
                peso_v = partes[3] if len(partes) > 3 else "0"
                self.vertices[vid] = {'rotulo': rotulo, 'peso': peso_v}
                idx += 1

            m = int(linhas[idx]); idx += 1

            for _ in range(m):
                partes = linhas[idx].split()
                u, v, w = int(partes[0]), int(partes[1]), float(partes[2])
                self.adj[u].append((v, w))
                if self._eh_nao_orientado():
                    self.adj[v].append((u, w))
                idx += 1

            print(f"[OK] Grafo carregado: {len(self.vertices)} vertices, "
                  f"{self._contar_arestas()} arestas.")
        except FileNotFoundError:
            print(f"[!] Arquivo '{caminho}' nao encontrado.")
        except Exception as e:
            print(f"[!] Erro ao ler arquivo: {e}")

    def gravar_arquivo(self, caminho):
        """
        Grava o grafo no arquivo texto no formato padrao da disciplina.
        Para grafos nao orientados, cada aresta e gravada uma unica vez
        (com o menor ID primeiro).
        """
        try:
            with open(caminho, 'w', encoding='utf-8') as f:
                f.write(f"{self.tipo}\n")
                f.write(f"{len(self.vertices)}\n")
                for vid in sorted(self.vertices):
                    r = self.vertices[vid]['rotulo']
                    p = self.vertices[vid]['peso']
                    f.write(f'{vid} "{r}" "{p}"\n')

                # Coleta arestas sem duplicatas para grafos nao orientados
                arestas = []
                vistas = set()
                for u in sorted(self.adj):
                    for v, w in self.adj[u]:
                        chave = (min(u, v), max(u, v)) if self._eh_nao_orientado() else (u, v)
                        if chave not in vistas:
                            vistas.add(chave)
                            arestas.append((chave[0], chave[1], w))

                f.write(f"{len(arestas)}\n")
                for u, v, w in arestas:
                    f.write(f"{u} {v} {w}\n")

            print(f"[OK] Grafo gravado em '{caminho}' com sucesso.")
        except Exception as e:
            print(f"[!] Erro ao gravar arquivo: {e}")

    # ------------------------------------------------------------------
    # Insercao e remocao
    # ------------------------------------------------------------------

    def inserir_vertice(self, vid, rotulo, peso="0"):
        """Adiciona um vertice ao grafo se o ID ainda nao existir."""
        if vid in self.vertices:
            print(f"[!] Vertice {vid} ja existe.")
        else:
            self.vertices[vid] = {'rotulo': rotulo, 'peso': peso}
            print(f"[OK] Vertice '{rotulo}' (ID {vid}) inserido.")

    def inserir_aresta(self, u, v, peso=1.0):
        """Adiciona uma aresta entre u e v com o peso indicado."""
        if u not in self.vertices or v not in self.vertices:
            print("[!] Um ou ambos os vertices nao existem.")
            return
        if self._aresta_existe(u, v):
            print(f"[!] Aresta {u}-{v} ja existe.")
            return
        self.adj[u].append((v, peso))
        if self._eh_nao_orientado():
            self.adj[v].append((u, peso))
        seta = "<->" if self._eh_nao_orientado() else "->"
        print(f"[OK] Aresta {u} {seta} {v} (peso {peso}) inserida.")

    def remover_vertice(self, vid):
        """Remove um vertice e todas as suas arestas adjacentes."""
        if vid not in self.vertices:
            print(f"[!] Vertice {vid} nao encontrado.")
            return
        del self.vertices[vid]
        if vid in self.adj:
            del self.adj[vid]
        for u in self.adj:
            self.adj[u] = [(v, w) for v, w in self.adj[u] if v != vid]
        print(f"[OK] Vertice {vid} removido.")

    def remover_aresta(self, u, v):
        """Remove a aresta entre u e v."""
        if not self._aresta_existe(u, v):
            print(f"[!] Aresta {u}-{v} nao encontrada.")
            return
        self.adj[u] = [(viz, w) for viz, w in self.adj[u] if viz != v]
        if self._eh_nao_orientado():
            self.adj[v] = [(viz, w) for viz, w in self.adj[v] if viz != u]
        seta = "<->" if self._eh_nao_orientado() else "->"
        print(f"[OK] Aresta {u} {seta} {v} removida.")

    # ------------------------------------------------------------------
    # Exibicao
    # ------------------------------------------------------------------

    def mostrar_conteudo(self):
        """Exibe tipo, vertices (classificados) e as primeiras 20 arestas."""
        if not self.vertices:
            print("[!] Grafo vazio. Carregue um arquivo primeiro.")
            return

        tipos_desc = {
            0: "Nao orientado - sem peso",
            1: "Nao orientado - peso no vertice",
            2: "Nao orientado - peso na aresta",
            3: "Nao orientado - peso no vertice e na aresta",
            4: "Orientado - sem peso",
            5: "Orientado - peso no vertice",
            6: "Orientado - peso na aresta",
            7: "Orientado - peso no vertice e na aresta",
        }
        print("\n" + "="*60)
        print("  SismoGraph - Conteudo do Grafo")
        print("="*60)
        print(f"  Tipo     : {self.tipo} -> {tipos_desc.get(self.tipo, '?')}")
        print(f"  Vertices : {len(self.vertices)}")
        print(f"  Arestas  : {self._contar_arestas()}")
        print("-"*60)
        print(f"  {'ID':<5} {'Rotulo':<25} {'Tipo':<12} {'Peso'}")
        print(f"  {'----':<5} {'------':<25} {'----':<12} {'----'}")
        for vid in sorted(self.vertices):
            r = self.vertices[vid]['rotulo']
            p = self.vertices[vid]['peso']
            tp = self._tipo_vertice(vid)
            peso_exib = p if p != "0" else "-"
            print(f"  {vid:<5} {r:<25} {tp:<12} {peso_exib}")

        print("-"*60)
        print("  Primeiras 20 arestas:")
        vistas = set()
        contador = 0
        for u in sorted(self.adj):
            for v, w in self.adj[u]:
                chave = (min(u, v), max(u, v)) if self._eh_nao_orientado() else (u, v)
                if chave not in vistas and contador < 20:
                    vistas.add(chave)
                    ru = self.vertices[u]['rotulo'] if u in self.vertices else str(u)
                    rv = self.vertices[v]['rotulo'] if v in self.vertices else str(v)
                    seta = "<->" if self._eh_nao_orientado() else "->"
                    print(f"  {u}({ru}) {seta} {v}({rv})  [MMI {w}]")
                    contador += 1
        print("="*60)

    def mostrar_grafo(self):
        """Exibe a lista de adjacencia completa do grafo."""
        if not self.vertices:
            print("[!] Grafo vazio. Carregue um arquivo primeiro.")
            return

        print("\n" + "="*60)
        print("  Lista de Adjacencia - SismoGraph")
        print("="*60)
        for vid in sorted(self.vertices):
            if vid not in self.vertices:
                continue
            rotulo = self.vertices[vid]['rotulo']
            vizinhos = self.adj.get(vid, [])
            if vizinhos:
                # Exibe ate 5 vizinhos e indica quantos restam
                exibir = vizinhos[:5]
                resto = len(vizinhos) - 5
                viz_str = ", ".join(
                    f"{self.vertices[v]['rotulo']}({w})"
                    if v in self.vertices else f"{v}({w})"
                    for v, w in exibir
                )
                if resto > 0:
                    viz_str += f" ... +{resto}"
                print(f"  [{vid:>2}] {rotulo:<20} -> {viz_str}")
            else:
                print(f"  [{vid:>2}] {rotulo:<20} -> (isolado)")
        print("="*60)

    # ------------------------------------------------------------------
    # PARTE 2 - Analise de Conexidade
    # ------------------------------------------------------------------

    def _bfs_componentes(self):
        """
        BFS para encontrar componentes conexas em grafos nao orientados.
        Retorna lista de conjuntos, cada um representando uma componente.
        """
        visitados = set()
        componentes = []
        for origem in self.vertices:
            if origem not in visitados:
                componente = set()
                fila = deque([origem])
                visitados.add(origem)
                while fila:
                    atual = fila.popleft()
                    componente.add(atual)
                    for viz, _ in self.adj.get(atual, []):
                        if viz not in visitados and viz in self.vertices:
                            visitados.add(viz)
                            fila.append(viz)
                componentes.append(componente)
        return componentes

    def _dfs_ordem_finalizacao(self, origem, visitados, pilha):
        """DFS iterativa que registra a ordem de finalizacao (para Kosaraju)."""
        stack = [(origem, iter(self.adj.get(origem, [])))]
        visitados.add(origem)
        while stack:
            v, it = stack[-1]
            try:
                viz, _ = next(it)
                if viz not in visitados and viz in self.vertices:
                    visitados.add(viz)
                    stack.append((viz, iter(self.adj.get(viz, []))))
            except StopIteration:
                pilha.append(v)
                stack.pop()

    def _kosaraju(self):
        """
        Algoritmo de Kosaraju para componentes fortemente conexas
        em grafos orientados.
        Retorna lista de conjuntos (SCCs).
        """
        visitados = set()
        pilha = []
        for v in self.vertices:
            if v not in visitados:
                self._dfs_ordem_finalizacao(v, visitados, pilha)

        # Constroi grafo transposto
        transposto = defaultdict(list)
        for u in self.adj:
            for v, w in self.adj[u]:
                transposto[v].append((u, w))

        visitados.clear()
        sccs = []
        while pilha:
            v = pilha.pop()
            if v not in visitados:
                comp = set()
                stack = [v]
                visitados.add(v)
                while stack:
                    atual = stack.pop()
                    comp.add(atual)
                    for viz, _ in transposto.get(atual, []):
                        if viz not in visitados and viz in self.vertices:
                            visitados.add(viz)
                            stack.append(viz)
                sccs.append(comp)
        return sccs

    def conexidade(self):
        """
        Analisa a conexidade do grafo.
        - Nao orientado: BFS para encontrar componentes conexas.
        - Orientado    : Kosaraju para SCCs + verificacao de conectividade fraca.
        Exibe resultado formatado com listagem das componentes.
        """
        if not self.vertices:
            print("[!] Grafo vazio.")
            return

        print("\n" + "="*60)
        print("  Analise de Conexidade - SismoGraph")
        print("="*60)

        if self._eh_nao_orientado():
            componentes = self._bfs_componentes()
            if len(componentes) == 1:
                print("  Resultado : CONEXO")
                print(f"  Todos os {len(self.vertices)} vertices estao interligados.")
            else:
                print(f"  Resultado : DESCONEXO")
                print(f"  Componentes conexas encontradas: {len(componentes)}")
                for i, comp in enumerate(sorted(componentes, key=len, reverse=True), 1):
                    rotulos = [self.vertices[v]['rotulo'] for v in sorted(comp) if v in self.vertices]
                    exibir = rotulos[:5]
                    resto = len(rotulos) - 5
                    lista = ", ".join(exibir) + (f" ... +{resto}" if resto > 0 else "")
                    print(f"  Componente {i} ({len(comp)} vertices): {lista}")
        else:
            sccs = self._kosaraju()
            fortemente = all(len(s) == len(self.vertices) for s in sccs)
            if fortemente and len(sccs) == 1:
                print("  Resultado : FORTEMENTE CONEXO")
            else:
                print(f"  Resultado : NAO FORTEMENTE CONEXO")
                print(f"  SCCs encontradas: {len(sccs)}")
                for i, scc in enumerate(sorted(sccs, key=len, reverse=True)[:5], 1):
                    rotulos = [self.vertices[v]['rotulo'] for v in sorted(scc) if v in self.vertices]
                    print(f"  SCC {i} ({len(scc)} vertices): {', '.join(rotulos[:4])}")
        print("="*60)

    # ------------------------------------------------------------------
    # PARTE 3 - Item 1: Dijkstra (Caminho de Maior Intensidade Sismica)
    # ------------------------------------------------------------------

    def caminho_maior_intensidade(self, origem, destino):
        """
        Calcula o caminho de MAIOR intensidade sismica acumulada entre
        dois vertices usando Dijkstra com pesos invertidos.

        Justificativa: as arestas representam intensidade MMI. Para
        encontrar o caminho que maximiza a intensidade total percebida,
        invertemos o problema: usamos (peso_maximo - peso_aresta) como
        custo, minimizando esse custo equivale a maximizar a intensidade.
        Isso tem sentido sismologico: identifica a rota de propagacao
        de maior impacto entre epicentro e cidade.

        Parametros:
            origem  (int): ID do vertice de partida (tipicamente epicentro)
            destino (int): ID do vertice de chegada (tipicamente cidade)
        """
        if origem not in self.vertices or destino not in self.vertices:
            print("[!] Um ou ambos os vertices nao existem.")
            return
        if origem == destino:
            print("[!] Origem e destino devem ser diferentes.")
            return

        # Peso maximo para inverter (MMI maximo e 12.0 neste grafo)
        W_MAX = 12.0

        # dist[v] = custo invertido acumulado minimo ate v
        dist = {v: math.inf for v in self.vertices}
        dist[origem] = 0.0
        anterior = {v: None for v in self.vertices}

        # Fila de prioridade: (custo_invertido, vertice)
        heap = [(0.0, origem)]

        while heap:
            custo_atual, u = heapq.heappop(heap)
            if custo_atual > dist[u]:
                continue
            if u == destino:
                break
            for v, w in self.adj.get(u, []):
                if v not in self.vertices:
                    continue
                custo_aresta = W_MAX - w   # inverte: maior MMI = menor custo
                novo_custo = dist[u] + custo_aresta
                if novo_custo < dist[v]:
                    dist[v] = novo_custo
                    anterior[v] = u
                    heapq.heappush(heap, (novo_custo, v))

        print("\n" + "="*60)
        print("  Caminho de Maior Intensidade Sismica (Dijkstra)")
        print("="*60)

        if dist[destino] == math.inf:
            print(f"  [!] Nao existe caminho entre {origem} e {destino}.")
            print("="*60)
            return

        # Reconstroi o caminho
        caminho = []
        atual = destino
        while atual is not None:
            caminho.append(atual)
            atual = anterior[atual]
        caminho.reverse()

        # Calcula a intensidade real acumulada do caminho
        intensidade_total = 0.0
        print(f"\n  De : {self.vertices[origem]['rotulo']} (ID {origem})")
        print(f"  Para: {self.vertices[destino]['rotulo']} (ID {destino})")
        print(f"\n  Caminho encontrado:")
        for i in range(len(caminho) - 1):
            u, v = caminho[i], caminho[i+1]
            peso_uv = next((w for viz, w in self.adj[u] if viz == v), 0)
            intensidade_total += peso_uv
            ru = self.vertices[u]['rotulo']
            rv = self.vertices[v]['rotulo']
            print(f"    {ru} --> {rv}  [MMI {peso_uv}]")

        print(f"\n  Vertices no caminho  : {len(caminho)}")
        print(f"  Arestas percorridas  : {len(caminho)-1}")
        print(f"  Intensidade acumulada: {intensidade_total:.1f} MMI")
        print(f"\n  Interpretacao: este e o percurso que propaga a maior")
        print(f"  intensidade sismica acumulada entre os dois pontos.")
        print("="*60)

    # ------------------------------------------------------------------
    # PARTE 3 - Item 2a: Grau dos Vertices
    # ------------------------------------------------------------------

    def analise_grau(self):
        """
        Calcula e exibe o grau de todos os vertices, destacando os de
        maior e menor grau. Para grafos nao orientados, grau = numero
        de vizinhos. Para orientados, exibe grau de entrada e saida.

        Relevancia sismologica: cidades com maior grau estao conectadas
        a mais epicentros, indicando maior vulnerabilidade sismica.
        """
        if not self.vertices:
            print("[!] Grafo vazio.")
            return

        graus = {}
        for vid in self.vertices:
            graus[vid] = len(self.adj.get(vid, []))

        ordenados = sorted(graus.items(), key=lambda x: x[1], reverse=True)

        print("\n" + "="*60)
        print("  Analise de Grau dos Vertices - SismoGraph")
        print("="*60)
        print(f"  Grau maximo: {ordenados[0][1]}  "
              f"({self.vertices[ordenados[0][0]]['rotulo']})")
        print(f"  Grau minimo: {ordenados[-1][1]}  "
              f"({self.vertices[ordenados[-1][0]]['rotulo']})")
        grau_medio = sum(graus.values()) / len(graus)
        print(f"  Grau medio : {grau_medio:.2f}")

        print(f"\n  Top 10 vertices com MAIOR grau (mais vulneraveis):")
        print(f"  {'ID':<5} {'Rotulo':<25} {'Tipo':<12} {'Grau'}")
        print(f"  {'-'*55}")
        for vid, grau in ordenados[:10]:
            tp = self._tipo_vertice(vid)
            print(f"  {vid:<5} {self.vertices[vid]['rotulo']:<25} {tp:<12} {grau}")

        print(f"\n  Top 5 vertices com MENOR grau (menos conectados):")
        print(f"  {'ID':<5} {'Rotulo':<25} {'Tipo':<12} {'Grau'}")
        print(f"  {'-'*55}")
        for vid, grau in ordenados[-5:]:
            tp = self._tipo_vertice(vid)
            print(f"  {vid:<5} {self.vertices[vid]['rotulo']:<25} {tp:<12} {grau}")

        # Vertices isolados
        isolados = [vid for vid, g in graus.items() if g == 0]
        if isolados:
            nomes = [self.vertices[v]['rotulo'] for v in isolados]
            print(f"\n  Vertices isolados (grau 0): {', '.join(nomes)}")
        else:
            print(f"\n  Nenhum vertice isolado encontrado.")
        print("="*60)

    # ------------------------------------------------------------------
    # PARTE 3 - Item 2b: Verificacao Euleriana
    # ------------------------------------------------------------------

    def verificacao_euleriana(self):
        """
        Verifica se o grafo admite circuito ou percurso euleriano.

        Criterios (grafo nao orientado conexo):
          - Circuito euleriano : todos os vertices tem grau par.
          - Percurso euleriano : exatamente 2 vertices tem grau impar.
          - Nenhum            : mais de 2 vertices com grau impar.

        Criterios (grafo orientado):
          - Circuito: grau_entrada == grau_saida para todos os vertices.
          - Percurso: exatamente 1 vertice com saida - entrada = 1
                      e exatamente 1 com entrada - saida = 1.

        Relevancia: um circuito euleriano existindo significaria que e
        possivel percorrer toda a rede sismica passando por cada conexao
        exatamente uma vez, voltando ao ponto de partida.
        """
        if not self.vertices:
            print("[!] Grafo vazio.")
            return

        print("\n" + "="*60)
        print("  Verificacao Euleriana - SismoGraph")
        print("="*60)

        # Verifica conexidade primeiro (ignora isolados)
        componentes = self._bfs_componentes() if self._eh_nao_orientado() else []
        nao_isolados = [c for c in componentes if len(c) > 1]
        conexo = len(nao_isolados) <= 1

        if self._eh_nao_orientado():
            graus_impares = []
            for vid in self.vertices:
                grau = len(self.adj.get(vid, []))
                if grau % 2 != 0:
                    graus_impares.append((vid, grau))

            print(f"  Grafo conexo (excluindo isolados): {'Sim' if conexo else 'Nao'}")
            print(f"  Vertices com grau impar: {len(graus_impares)}")

            if not conexo:
                print("\n  Resultado: NAO admite Euleriano (grafo desconexo).")
            elif len(graus_impares) == 0:
                print("\n  Resultado: ADMITE CIRCUITO EULERIANO")
                print("  Todos os vertices possuem grau par.")
                print("  E possivel percorrer todas as conexoes sismicas exatamente")
                print("  uma vez e retornar ao ponto de partida.")
            elif len(graus_impares) == 2:
                v1, g1 = graus_impares[0]
                v2, g2 = graus_impares[1]
                print("\n  Resultado: ADMITE PERCURSO EULERIANO (mas nao circuito)")
                print(f"  Exatamente 2 vertices com grau impar:")
                print(f"    - {self.vertices[v1]['rotulo']} (ID {v1}, grau {g1})")
                print(f"    - {self.vertices[v2]['rotulo']} (ID {v2}, grau {g2})")
                print(f"  O percurso euleriano deve iniciar em um desses vertices")
                print(f"  e terminar no outro.")
            else:
                print(f"\n  Resultado: NAO admite Euleriano")
                print(f"  Ha {len(graus_impares)} vertices com grau impar (necessario 0 ou 2).")
                print("  Exemplos de vertices com grau impar:")
                for vid, grau in graus_impares[:5]:
                    print(f"    - {self.vertices[vid]['rotulo']} (grau {grau})")
        else:
            # Orientado: compara grau de entrada e saida
            grau_saida = {v: len(self.adj.get(v, [])) for v in self.vertices}
            grau_entrada = defaultdict(int)
            for u in self.adj:
                for v, _ in self.adj[u]:
                    if v in self.vertices:
                        grau_entrada[v] += 1

            dif_positiva = [(v, grau_saida[v] - grau_entrada[v])
                            for v in self.vertices if grau_saida[v] - grau_entrada[v] == 1]
            dif_negativa = [(v, grau_entrada[v] - grau_saida[v])
                            for v in self.vertices if grau_entrada[v] - grau_saida[v] == 1]
            equilibrados = all(grau_saida[v] == grau_entrada[v] for v in self.vertices)

            if equilibrados:
                print("\n  Resultado: ADMITE CIRCUITO EULERIANO (orientado)")
            elif len(dif_positiva) == 1 and len(dif_negativa) == 1:
                print("\n  Resultado: ADMITE PERCURSO EULERIANO (orientado)")
            else:
                print("\n  Resultado: NAO admite Euleriano (orientado)")
        print("="*60)

    # ------------------------------------------------------------------
    # PARTE 3 - Item 2c: Verificacao Hamiltoniana (heuristica)
    # ------------------------------------------------------------------

    def verificacao_hamiltoniana(self):
        """
        Verifica se o grafo PODE admitir ciclo/caminho hamiltoniano
        usando o Teorema de Ore e o Teorema de Dirac como condicoes
        suficientes.

        Teorema de Dirac: se todo vertice tem grau >= n/2, o grafo
        admite ciclo hamiltoniano.

        Teorema de Ore: se para todo par de vertices nao adjacentes u,v
        temos grau(u) + grau(v) >= n, entao existe ciclo hamiltoniano.

        Observacao: esses teoremas fornecem condicoes suficientes, nao
        necessarias. O problema hamiltoniano e NP-completo, portanto
        nao e verificado por forca bruta para grafos grandes.

        Relevancia: um ciclo hamiltoniano representaria uma rota de
        inspecao sismica passando por cada cidade/epicentro exatamente
        uma vez.
        """
        if not self.vertices:
            print("[!] Grafo vazio.")
            return

        n = len(self.vertices)
        graus = {vid: len(self.adj.get(vid, [])) for vid in self.vertices}
        ids = list(self.vertices.keys())

        print("\n" + "="*60)
        print("  Verificacao Hamiltoniana - SismoGraph")
        print("="*60)
        print(f"  Vertices: {n}  |  Arestas: {self._contar_arestas()}")

        # Criterio de Dirac
        grau_min = min(graus.values())
        dirac = grau_min >= n / 2
        print(f"\n  [Teorema de Dirac]")
        print(f"  Grau minimo encontrado : {grau_min}")
        print(f"  n/2 = {n/2:.1f}")
        print(f"  Condicao (grau_min >= n/2): {'SATISFEITA' if dirac else 'NAO satisfeita'}")

        # Criterio de Ore (amostra - para grafos grandes verifica pares criticos)
        print(f"\n  [Teorema de Ore]")
        ore_ok = True
        par_falhou = None
        # Verifica pares nao adjacentes (amostragem para eficiencia)
        conjunto_adj = {v: set(viz for viz, _ in self.adj.get(v, []))
                        for v in self.vertices}
        verificados = 0
        for i in range(min(len(ids), 50)):   # amostra os primeiros 50
            for j in range(i + 1, min(len(ids), 50)):
                u, v = ids[i], ids[j]
                if v not in conjunto_adj[u]:  # nao adjacentes
                    if graus[u] + graus[v] < n:
                        ore_ok = False
                        par_falhou = (u, v)
                        break
                    verificados += 1
            if not ore_ok:
                break

        if par_falhou:
            u, v = par_falhou
            print(f"  Par nao adjacente encontrado onde grau(u)+grau(v) < n:")
            print(f"    {self.vertices[u]['rotulo']} (grau {graus[u]}) + "
                  f"{self.vertices[v]['rotulo']} (grau {graus[v]}) = "
                  f"{graus[u]+graus[v]} < {n}")
            print(f"  Condicao de Ore: NAO satisfeita (na amostra verificada)")
        else:
            print(f"  Condicao de Ore: SATISFEITA na amostra de pares verificados")

        print(f"\n  Resultado:")
        if dirac:
            print("  O grafo PROVAVELMENTE ADMITE CICLO HAMILTONIANO")
            print("  (condicao suficiente de Dirac satisfeita).")
        elif ore_ok:
            print("  O grafo POSSIVELMENTE ADMITE CICLO HAMILTONIANO")
            print("  (condicao de Ore satisfeita na amostra).")
        else:
            print("  As condicoes suficientes classicas NAO foram satisfeitas.")
            print("  Isso nao garante a inexistencia de ciclo hamiltoniano,")
            print("  pois o problema e NP-completo.")

        print(f"\n  Interpretacao sismologica: um ciclo hamiltoniano")
        print(f"  representaria uma rota de inspecao que visita cada")
        print(f"  cidade e epicentro exatamente uma vez.")
        print("="*60)

    # ------------------------------------------------------------------
    # PARTE 3 - Item 2d: Arvore Geradora Minima (Kruskal)
    # ------------------------------------------------------------------

    def arvore_geradora_minima(self):
        """
        Calcula a Arvore Geradora Minima (AGM) usando o algoritmo de
        Kruskal com Union-Find (estrutura Disjoint Set Union).

        A AGM conecta todos os vertices com o menor custo total de
        arestas. No contexto sismologico, como os pesos sao intensidades
        MMI (maiores = mais perigosos), a AGM representa a rede de
        conexoes sismicas de MENOR intensidade total, ou seja, a
        'espinha dorsal' de menor impacto que ainda mantem todos os
        pontos interligados.

        Complexidade: O(m log m), onde m e o numero de arestas.
        """
        if not self.vertices:
            print("[!] Grafo vazio.")
            return
        if not self._eh_nao_orientado():
            print("[!] AGM (Kruskal) e aplicavel apenas a grafos nao orientados.")
            return

        # Coleta todas as arestas sem duplicatas
        arestas = []
        vistas = set()
        for u in self.adj:
            for v, w in self.adj[u]:
                chave = (min(u, v), max(u, v))
                if chave not in vistas:
                    vistas.add(chave)
                    arestas.append((w, u, v))
        arestas.sort()  # ordena por peso crescente

        # Union-Find
        pai = {v: v for v in self.vertices}
        rank = {v: 0 for v in self.vertices}

        def encontrar(x):
            while pai[x] != x:
                pai[x] = pai[pai[x]]  # compressao de caminho
                x = pai[x]
            return x

        def unir(x, y):
            rx, ry = encontrar(x), encontrar(y)
            if rx == ry:
                return False
            if rank[rx] < rank[ry]:
                rx, ry = ry, rx
            pai[ry] = rx
            if rank[rx] == rank[ry]:
                rank[rx] += 1
            return True

        agm = []
        peso_total = 0.0
        for w, u, v in arestas:
            if unir(u, v):
                agm.append((u, v, w))
                peso_total += w
                if len(agm) == len(self.vertices) - 1:
                    break

        print("\n" + "="*60)
        print("  Arvore Geradora Minima (Kruskal) - SismoGraph")
        print("="*60)

        if len(agm) < len(self.vertices) - 1:
            print("  [!] Grafo desconexo: AGM nao cobre todos os vertices.")
            print(f"  Arestas incluidas: {len(agm)} (esperado: {len(self.vertices)-1})")
        else:
            print(f"  AGM calculada com sucesso!")
            print(f"  Arestas na AGM    : {len(agm)}")
            print(f"  Peso total (MMI)  : {peso_total:.1f}")
            print(f"  Peso medio (MMI)  : {peso_total/len(agm):.2f}")

        print(f"\n  Primeiras 15 arestas da AGM (menor intensidade):")
        print(f"  {'De':<22} {'Para':<22} {'MMI'}")
        print(f"  {'-'*55}")
        for u, v, w in agm[:15]:
            ru = self.vertices[u]['rotulo'] if u in self.vertices else str(u)
            rv = self.vertices[v]['rotulo'] if v in self.vertices else str(v)
            print(f"  {ru:<22} {rv:<22} {w}")
        if len(agm) > 15:
            print(f"  ... e mais {len(agm)-15} arestas.")

        print(f"\n  Interpretacao sismologica:")
        print(f"  A AGM representa a rede de {len(agm)} conexoes de menor")
        print(f"  intensidade sismica que ainda mantem todos os {len(self.vertices)}")
        print(f"  pontos interligados. Intensidade media na AGM: "
              f"{peso_total/len(agm):.2f} MMI,")
        print(f"  contra {sum(w for _,_,w in arestas)/len(arestas):.2f} MMI de media das arestas do grafo.")
        print("="*60)


# =============================================================================
# MENU PRINCIPAL
# =============================================================================

def exibir_menu():
    """Exibe o cabecalho e o menu de opcoes."""
    sep = "+" + "-"*56 + "+"
    print()
    print(sep)
    print("      SismoGraph - Analise de Impacto Sismico na Asia")
    print("  Luiz Fernando Ferrari Batistela   - RA 10427397")
    print("  Henrique Jeam Lima                - RA 10277156")
    print(sep)
    print("  a) Ler dados do arquivo grafo.txt")
    print("  b) Gravar dados no arquivo grafo.txt")
    print("  c) Inserir vertice")
    print("  d) Inserir aresta")
    print("  e) Remover vertice")
    print("  f) Remover aresta")
    print("  g) Mostrar conteudo do arquivo")
    print("  h) Mostrar grafo (lista de adjacencia)")
    print("  i) Apresentar conexidade e grafo reduzido")
    print("  -- Parte 3 -----------------------------------------")
    print("  j) Caminho de maior intensidade sismica (Dijkstra)")
    print("  k) Analise de grau dos vertices")
    print("  l) Verificacao euleriana")
    print("  m) Verificacao hamiltoniana")
    print("  n) Arvore geradora minima (Kruskal)")
    print("  o) Encerrar aplicacao")
    print(sep)

def main():
    """Loop principal da aplicacao SismoGraph."""
    grafo = Grafo()

    while True:
        exibir_menu()
        opcao = input("  Opcao: ").strip().lower()

        # -- Opcoes originais (Partes 1 e 2) --------------------------

        if opcao == 'a':
            caminho = input("  Caminho do arquivo [grafo.txt]: ").strip()
            if not caminho:
                caminho = "grafo.txt"
            grafo.ler_arquivo(caminho)

        elif opcao == 'b':
            caminho = input("  Caminho do arquivo [grafo.txt]: ").strip()
            if not caminho:
                caminho = "grafo.txt"
            grafo.gravar_arquivo(caminho)

        elif opcao == 'c':
            print("  -- Inserir Vertice --")
            try:
                vid = int(input("  ID do vertice: "))
                rotulo = input("  Rotulo (nome): ")
                peso = input("  Peso (0 se nao aplicavel): ").strip() or "0"
                grafo.inserir_vertice(vid, rotulo, peso)
            except ValueError:
                print("  [!] ID invalido.")

        elif opcao == 'd':
            print("  -- Inserir Aresta --")
            try:
                u = int(input("  ID vertice origem : "))
                v = int(input("  ID vertice destino: "))
                w = float(input("  Peso da aresta (MMI): "))
                grafo.inserir_aresta(u, v, w)
            except ValueError:
                print("  [!] Entrada invalida.")

        elif opcao == 'e':
            print("  -- Remover Vertice --")
            try:
                vid = int(input("  ID do vertice a remover: "))
                grafo.remover_vertice(vid)
            except ValueError:
                print("  [!] ID invalido.")

        elif opcao == 'f':
            print("  -- Remover Aresta --")
            try:
                u = int(input("  ID vertice origem : "))
                v = int(input("  ID vertice destino: "))
                grafo.remover_aresta(u, v)
            except ValueError:
                print("  [!] Entrada invalida.")

        elif opcao == 'g':
            grafo.mostrar_conteudo()

        elif opcao == 'h':
            grafo.mostrar_grafo()

        elif opcao == 'i':
            grafo.conexidade()

        # -- Novas opcoes (Parte 3) ------------------------------------

        elif opcao == 'j':
            print("  -- Caminho de Maior Intensidade Sismica (Dijkstra) --")
            print("  Dica: IDs 0-39 = cidades | IDs 40-69 = epicentros")
            try:
                origem = int(input("  ID do vertice de origem : "))
                destino = int(input("  ID do vertice de destino: "))
                grafo.caminho_maior_intensidade(origem, destino)
            except ValueError:
                print("  [!] Entrada invalida.")

        elif opcao == 'k':
            grafo.analise_grau()

        elif opcao == 'l':
            grafo.verificacao_euleriana()

        elif opcao == 'm':
            grafo.verificacao_hamiltoniana()

        elif opcao == 'n':
            grafo.arvore_geradora_minima()

        elif opcao == 'o':
            print("\n  Encerrando SismoGraph. Obrigado!")
            print("  Universidade Presbiteriana Mackenzie -- Teoria dos Grafos 6G\n")
            break

        else:
            print("  [!] Opcao invalida. Escolha entre a e o.")


if __name__ == "__main__":
    main()

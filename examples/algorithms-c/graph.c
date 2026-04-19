/**
 * graph.c - C语言图算法实现
 * 包含：BFS、DFS
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>

#define MAX_VERTICES 100

typedef struct {
    int adj[MAX_VERTICES][MAX_VERTICES];
    int n;
} Graph;

void init_graph(Graph* g, int n) {
    g->n = n;
    for (int i = 0; i < n; i++)
        for (int j = 0; j < n; j++)
            g->adj[i][j] = 0;
}

void add_edge(Graph* g, int u, int v) {
    g->adj[u][v] = 1;
    g->adj[v][u] = 1; // undirected
}

void bfs(const Graph* g, int start, int visited[], int order[], int* order_count) {
    int queue[MAX_VERTICES];
    int front = 0, rear = 0;
    memset(visited, 0, g->n * sizeof(int));
    *order_count = 0;
    
    visited[start] = 1;
    queue[rear++] = start;
    
    while (front < rear) {
        int v = queue[front++];
        order[(*order_count)++] = v;
        for (int i = 0; i < g->n; i++) {
            if (g->adj[v][i] && !visited[i]) {
                visited[i] = 1;
                queue[rear++] = i;
            }
        }
    }
}

void dfs(const Graph* g, int v, int visited[], int order[], int* order_count) {
    visited[v] = 1;
    order[(*order_count)++] = v;
    for (int i = 0; i < g->n; i++) {
        if (g->adj[v][i] && !visited[i]) {
            dfs(g, i, visited, order, order_count);
        }
    }
}

int main() {
    Graph g;
    init_graph(&g, 4);
    add_edge(&g, 0, 1);
    add_edge(&g, 0, 2);
    add_edge(&g, 1, 2);
    add_edge(&g, 2, 3);
    
    int visited[4], order[4], count;
    bfs(&g, 0, visited, order, &count);
    assert(count == 4);
    assert(order[0] == 0);
    
    memset(visited, 0, sizeof(visited));
    count = 0;
    dfs(&g, 0, visited, order, &count);
    assert(count == 4);
    assert(order[0] == 0);
    
    printf("All graph tests passed!\n");
    return 0;
}

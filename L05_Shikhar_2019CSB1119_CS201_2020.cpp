#include<bits/stdc++.h>
using namespace std;

#define f(i,b) for(int (i)=0;(i)<(b);(i)++)
#define endl '\n'
#define pb push_back
#define mp make_pair
#define p1(x) x.first
#define p2(x) x.second
#define px1(x) x->first
#define px2(x) x->second
#define fastio                        \
    ios_base::sync_with_stdio(false); \
    cin.tie(NULL);                    \
    cout.tie(NULL);

set<pair<int,int>> final_edges;
//It makes it easier to have answer in global for recursive calls

int min_spec(int x, int y){
    //this function makes sure that if there are a->b multiple edges, then this would help select the smaller one
    //initialised with negative numbers as maximum edge weight was unknown to me at that time.
    if(x < 0 || x > y){
        return y;
    }
    return x;
}
int find_cycle_vertices(set<int> &C, map<int,int> minimum_in, int s, int n){
    //now we have to check each vertex and check if the we get a loop
    vector<int> V_min(n+1,-1);
    for(map<int,int>::iterator i = minimum_in.begin(); i != minimum_in.end(); i++){
        V_min[px1(i)] = px2(i);
        //store parent corresponding to min_edge
    }
    int found = 0;
    f(i,n){
        if(i+1 == s)//skip the source
            continue;
        //BFS for each vertex in the graph
        vector<int> vis(n+1,0);
        queue<int> q;
        q.push(i+1);
        vis[i+1] = 1;
        while(q.size()){
            int ref = q.front();
            q.pop();
            if(V_min[ref] == -1)
                break;
            if(vis[V_min[ref]] == 1){
                //if the vertex is identified again then it's a part of a cycle
                found = V_min[ref];
                break;    
            }
            q.push(V_min[ref]);
            vis[V_min[ref]] = 1;
        }
        if(found)
            break;
    }
    if(found){
        //insert all edges of the cycle
        int tracker = minimum_in[found];
        C.insert(minimum_in[found]);
        while(tracker != found){
            C.insert(minimum_in[tracker]);
            tracker = minimum_in[tracker];
        }
    }
    return found;
}

void update_minimum_in(map<int,int> &in, set<pair<int,int>> G, map<pair<int,int>,int> &W, set<int> V, int sup){
    
    vector<set<pair<int,int>>> edges(sup+1);
    //stores edges sorted by weight and then by source (second preference)
    for(set<pair<int,int>>::iterator j = G.begin(); j != G.end(); j++){
        edges[px2(j)].insert(mp(W[*(j)],px1(j)));
    }
    for(set<int>::iterator i = V.begin(); i != V.end(); i++){
        //min for each inserted
        if(edges[*(i)].size() != 0)
            in.insert({*(i), px2(edges[*(i)].begin())});
    }
    int min_sup = px1(edges[sup].begin());
    for(set<pair<int,int>>::iterator j = edges[sup].begin(); j != edges[sup].end(); j++){
        //updates edges around super node
        W[mp(px2(j),sup)] = W[mp(px2(j),sup)] - min_sup;
    }
}

int map_check(map<pair<int,int>,int> W, pair<int,int> edge){
    if(W.find(edge) != W.end()){
        return W[edge];
    }
    return -1;
}

//minimum cost arborescene
void arborescence(set<int> V, set<pair<int,int>> G, map<int,int> minimum_in, map<pair<int,int>,int> W, int s, int n){

    set<int> C;
    int cycle_confirm = find_cycle_vertices(C, minimum_in, s, n);
    //finds cycle vertices and also confirms the absence of a cycle
    
    if(!cycle_confirm){
        for(map<int,int>::iterator i = minimum_in.begin(); i != minimum_in.end(); i++)
            final_edges.insert(mp(px2(i),px1(i)));
        return;
    }
    //if there's a cycle than we'll have to replace with a super node
    //let super node be n+1
    int super_node = n+1;
    set<int> updated_V;
    map<pair<int,int>,int> updated_W;
    set<pair<int,int>> updated_G;
    map<pair<int,int>,pair<int,int>> past_reference;

    //could have used a double dimension array but that would have 10^6 elements for 1000 nodes in graph
    //this could be a problem in a recursive solution and I didn't want it to show stackoverflow for large
    //number of vertices, a map prevents that to some extent but adds log(E) time to the solution
    map<int,int> updated_min_in;

    updated_V.insert(n+1);
    for(set<int>::iterator i = V.begin();i != V.end();i++)
    {
        //all the edges not belonging to the cycle is inserted here
       if(C.find(*(i)) == C.end()){
           updated_V.insert(*(i));
       }
    }
    //above updates vertices after replacing cycle with super node
    
    for(set<pair<int,int>>::iterator i = G.begin(); i!=G.end(); i++){
        //in the given edges update according to super node
        //contract the graph to it's new state and then
        //a new smaller graph emerges, let's make that graph

        if(C.find(px1(i)) == C.end() && C.find(px2(i)) == C.end()){
            //if the edge doesn't have anything to do with the cycle, it remains unchanged
            updated_G.insert(*(i));
            updated_W[*(i)] = W[*(i)];
            past_reference[*(i)] = *(i);
        }
        else if(C.find(px1(i)) != C.end() && C.find(px2(i)) == C.end()){
            //if u is the part of cycle, super_node->v
            //now it's possible that more than one cycle vertex is pointing to v
            if(updated_G.find(mp(super_node,px2(i))) == updated_G.end() || W[*(i)] < map_check(updated_W, mp(super_node,px2(i)))){
                updated_W[mp(super_node,px2(i))] = W[*(i)];
                past_reference[mp(super_node,px2(i))] = *(i);
                updated_G.insert(mp(super_node,px2(i)));
            }
        }
        else if(C.find(px1(i)) == C.end() && C.find(px2(i)) != C.end()){
            //if v is part of the cycle
            //now it's possible that some u2->v is already a part
            //we'll check if it is and keep it if it's of lower weight
            //or update weight and mapping
            if(updated_G.find(mp(px1(i),super_node)) == updated_G.end() || W[*(i)] < map_check(updated_W, mp(px1(i),super_node))){
                updated_W[mp(px1(i),super_node)] = W[*(i)];
                past_reference[mp(px1(i),super_node)] = *(i);
                updated_G.insert(mp(px1(i),super_node));
            }
        }
    }
    //find the minimum_incoming edges in the contracted graph
    // and also update the edges around the super node
    update_minimum_in(updated_min_in, updated_G, updated_W, updated_V, super_node);
    
    arborescence(updated_V, updated_G, updated_min_in, updated_W, s, super_node);
    
    //expansion
    pair<int,int> cyc_edge = mp(-1,-1);
    set<pair<int,int>> temp_holder;
    for(set<pair<int,int>>::iterator i = final_edges.begin(); i != final_edges.end(); i++){
        //here the cycle edge in the cycle is identified that will be removed
        if(super_node == px2(i))
            cyc_edge = mp(minimum_in[p2(past_reference[*(i)])],p2(past_reference[*(i)]));
        temp_holder.insert(past_reference[*(i)]);
    }
    if(cyc_edge != mp(-1,-1)){
        //if no edge pointing to super node identified, then that cycle in itself was unreachable
        for(set<int>::iterator i = C.begin(); i != C.end(); i++){
            if(mp(minimum_in[*(i)],*(i)) != cyc_edge)
                temp_holder.insert(mp(minimum_in[*(i)],*(i)));
        }
    }
    //updating answer
    final_edges.clear();
    for(set<pair<int,int>>::iterator i = temp_holder.begin(); i != temp_holder.end(); i++){
        final_edges.insert(*(i));
    }
}

void print_answer(set<pair<int,int>> T, vector<vector<int>> W, int s, int n){
    vector<vector<int>> adjacent_children(n+1);
    vector<int> parent(n+1,-1);
    parent[s] = 0;
    int sum = 0;
    for(set<pair<int,int>>::iterator i = T.begin(); i != T.end(); i++){
        adjacent_children[px1(i)].pb(px2(i));
        parent[px2(i)] = px1(i);
        sum += W[px1(i)][px2(i)];
    }
    cout << sum << " ";
    vector<int> distance(n+1,-1);
    queue<int> q;
    q.push(s);
    distance[s] = 0;
    //BFS type updation of distance
    while(q.size()){
        int k = q.front();
        q.pop();
        f(j,adjacent_children[k].size()){
            distance[adjacent_children[k][j]] = distance[k] + W[k][adjacent_children[k][j]];
            q.push(adjacent_children[k][j]); 
        }
    }
    f(i,n){
        cout << distance[i+1] << " ";
    }
    cout << "# ";
    f(i,n){
        cout << parent[i+1] << " ";
    }
    cout << endl;
}

void update(set<pair<int,int>> G, set<int> &V, set<pair<int,int>> &G2, vector<int> visited){
    set<int> vis; //easy searching in log(n)
    
    f(i,visited.size()-1){//removes vertices unreached by source
        if(!visited[i+1]){
            V.erase(i+1);
        }
    }
    for(set<pair<int,int>>::iterator i = G.begin(); i != G.end(); i++){
        //removes edges for the same as above
        if(V.find(px1(i)) != V.end()){
            G2.insert(*(i));
        }
    }
}

void check_by_BFS_and_update(set<pair<int,int>> G, int s, set<pair<int,int>> &G3, set<int> &V, int n){
    vector<vector<int>> G2(n+1);
    for(set<pair<int,int>>::iterator i = G.begin(); i != G.end(); i++){
        G2[px1(i)].pb(px2(i));
    }
    //BFS approach to find the vertices that can be reached
    vector<int> visited(n+1,0); //this will keep track if the vertex was visited
    queue<int> q;
    q.push(s);
    visited[s] = 1;
    while(q.size()){
        int ref = q.front();
        q.pop();
        f(j,G2[ref].size()){
            if(!visited[G2[ref][j]]){
                visited[G2[ref][j]] = 1;
                q.push(G2[ref][j]);
            }
        }
    }
    update(G, V, G3, visited);//updates the graph by removing unvisited edges
}

int main(){
    fastio
    int t, m, n, s, a, b, w;
	cin >> t;
	while(t--){
	    cin >> n >> m >> s;
	    
	    vector<vector<int>> temp_incoming(n+1); //temp graph holder
	    vector<vector<int>> X(n+1,vector<int>(n+1,0));

	    set<pair<int,int>> G2; //graph
            set<int> V;
	    vector<int> incoming_min_edge(n+1,-1);
	    int flag = 0;
	    map<pair<int,int>,int> W;
            map<int,int> minimum_in;
            set<pair<int,int>> G;
	    
	    f(i,m){
	        cin >> a >> b >> w;
	        
	        if(b == s)
	            continue;
	        if(w < 0)
	            flag = 1;
	        if(G2.find(mp(a,b)) != G2.end()){
	            X[a][b] = min(X[a][b],w);
	            continue;
	        }
	        G2.insert(mp(a,b));
                V.insert(a);
                V.insert(b);
	        X[a][b] = w;
	    }
        //in the above graph, there will be certain vertices that are unreachable
        /*
        1
        4 3 1
        1 2 1
        1 3 2
        4 3 1
        in the above case, if we select the minimum incoming edges to a vertex,
        then 1->3 edge is not selected and 4->3 is selected, this selection doesn't
        induce a cycle, but that would result in 1->2 and 4->3 being the final selection,
        whereas the right answer is 1->2 and 1->3 as 2 & 3 both are reachable, to
        remove this possibility from occuring, we must remove vertices that are
        unreachable from the source vertex, this should make sure that unreachable
        edges don't interfere with the final answer.
        */
        //as discussed above, we will run BFS/DFS and check if it's possible to get to the vertices
        //and later remove the ones that weren't reached along with the edges going out of it
        check_by_BFS_and_update(G2, s, G, V, n);

        for(set<pair<int,int>>::iterator i = G.begin(); i != G.end(); i++){
            if(px2(i) == s){
                continue;
            }
            temp_incoming[px2(i)].pb(px1(i));
            incoming_min_edge[px2(i)] = min_spec(incoming_min_edge[px2(i)],X[px1(i)][px2(i)]);
        }

	    if(flag){
	        // -1 prints
            cout << -1 << endl;
	    }
	    else{
            f(i,n){
	            if(i+1 == s || !temp_incoming[i+1].size())
	                continue;
	            pair<int,int> edge1 = {n+1,n+1};
	            f(j,temp_incoming[i+1].size()){

	                W.insert({mp(temp_incoming[i+1][j],i+1),X[temp_incoming[i+1][j]][i+1]-incoming_min_edge[i+1]});
	                if(!(X[temp_incoming[i+1][j]][i+1]-incoming_min_edge[i+1]) && p1(edge1) > temp_incoming[i+1][j]){
                        //selects the minimum edge (if equal then u->v, u is minimized) and keeps track
	                    edge1 = mp(temp_incoming[i+1][j],i+1);
	                }
	            }
                minimum_in.insert({p2(edge1),p1(edge1)}); //maps vertex to minimum edge for easy access
	        }
	        //after this we have G', edge weight reduced but it doesn't
	        // affect the arborescence of the original graph
	        
	        arborescence(V, G, minimum_in, W, s, n);
            
            print_answer(final_edges, X, s, n);
            final_edges.clear();
	    }
	}
 }
/*I have checked my code on CodeChef IDE, my laptop, tutorialspoint IDE, I have also assumed
that C++ 14 or up will be used for evaluation. I have given n+1 and so on as super node label, 
mentioned in last FAQ in lab-05 document on GC, below is an input I checked against with the
corresponding output.
input :
2
4 5 1
1 2 6
2 3 2
1 3 6
4 2 5
3 4 1
4 3 1
1 2 1
1 3 2
4 3 1
output :
9 0 6 8 9 # 0 1 2 3
3 0 1 2 -1 # 0 1 1 -1
*/
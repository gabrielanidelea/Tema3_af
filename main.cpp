#include<iostream>
#include<fstream>
#include<queue>
#include<vector>
#include<stack>
#include <bits/stdc++.h>
using namespace std;
ifstream f("darb.in");
ofstream g("darb.out");
const int MAX=100001;
const int INF=0x3f3f3f3f;
class graf{
private:
    int n; //nr noduri //pt pb disjoint reprezinta nr de multimi
    int m; // nr muchii // pt pb disjoint repr nr de operatii
    vector <vector<pair<int, int>>> vector_costuri; //(pt apm)
    int vvect_disjoint[MAX]; // pt disjoint
    vector <vector<pair<int, int>>> vect_dijk;
    vector<vector<pair<int, int>>>vect_costuri_bellman;
    vector<int> graf_mf[1001]; // mf
    bool vizi_mf[1001]; // mf
    int capacitate[1001][1001], tati[1001]; // mf
    int mat[1001][1001]; // roy-floyd
    vector<int>v_darb[100001]; //darb
    int di[100001], nod_d; //vect de dst pt darb + nod

public:

    //------------------------Tema 2 -----------------------------
    //APM
    void citire_APM(); // functie pt creare gf
    void algoritm_APM(); // functie pt implementarea algoritmului lui prim



    //Disjoint
    int gaseste_radacina(int nod);
    void uneste(int nod1, int nod2);
    void algo_disjuncte();

    //Dijkstra
    void algo_dijk();

    //Bellman_Ford
    void algo_bellman_ford();


//--------------------Tema 3---------------------------------
    //MaxFlow
    void citire_mf();
    bool bfs_mf();
    void maxfl();
    void fct_mf();


    //Roy-Floyd
    void citire_rf();
    void fct_royf();

    //Diametrul unui Arbore
    void citire_darb();
    void dfs_darb(int nod1, int nod2, int &dimax);
    void fct_darb();

};
//----------darb---------
void graf:: citire_darb()
{
    int nod1, nod2;
    f >> n;
    for(int i = 1; i < n; i++)
    {
        f >> nod1 >> nod2;
        v_darb[nod1].push_back(nod2);
        v_darb[nod2].push_back(nod1);
    }
}
void graf:: dfs_darb(int nod1, int nod2, int &dimax)
{
    for(auto i: v_darb[nod1])
    {
        if(i == nod2) // daca nodul i este egal cu nodul 2
            continue; //iesim din if
        else
        { //daca este diferit
            di[i] = di[nod1] + 1; // adaugam in dreptul distantei nodului i distanta nodului1 + 1
            if(di[i] > dimax) // daca distanta din e mai mare decat diametrul maxim
            {
                dimax = di[i];
                nod_d = i; // nodul declarat global va primi val din i
            }
            dfs_darb(i, nod1, dimax); // apelam recurs dfs
        }
    }

}
void graf::fct_darb()
{
    int dimax = 0; // diam max e initial 0
    dfs_darb(1, 1, dimax);
    di[nod_d] = 0;
    dimax = 0;
    dfs_darb(nod_d, nod_d, dimax);
    g << di[nod_d] + 1; // afisam dist afer nodului updatat global + 1
}
//---------darb----------
//---------roy-floyd----------
void graf:: citire_rf()
{
    f >> n;
    for(int i = 1; i<=n; i++)
        for(int j = 1; j<=n; j++)
            f >> mat[i][j];

}
void graf:: fct_royf()
{
    for(int p = 1; p <= n; p++)
    {
        for(int i = 1; i<= n; i++)
        {
            for(int j = 1; j <= n; j++)
            {
                if(mat[i][p] && mat[p][j] &&(!mat[i][j] || mat[i][j] > mat[i][p] + mat[p][j]) && i!=j)
                {
                    mat[i][j] = mat[i][p] + mat[p][j];
                }
            }
        }
    }
    for(int i = 1; i<= n; i++)
    {
        for(int j = 1; j<=n; j++)
        {
            g << mat[i][j] << " ";

        }
        g << "\n";
    }
}
//---------roy-floyd--------------------
//---------maxflow----------------------

void graf:: citire_mf()
{
    f >> n >> m;
    for(int i = 0; i < m; i++)
    {
        int nod1, nod2;
        f >> nod1 >> nod2;
        f >> capacitate[nod1][nod2];
        graf_mf[nod1].push_back(nod2);
        graf_mf[nod2].push_back(nod1);
    }
}
bool graf:: bfs_mf()
{
    queue<int> coada_mf;
    coada_mf.push(1); //adaug 1 in coada
    vizi_mf[1] = true; //il marchez
    while(!coada_mf.empty()) // cat timp coada este nevida
    {
        auto nod_curent = coada_mf.front(); // tinem in nod_curent prima var din coada
        coada_mf.pop();
        for(auto i: graf_mf[nod_curent])
        {
            if(vizi_mf[i]!=0) continue; // daca vizi_mf[i] este vizitat
            if(capacitate[nod_curent][i] == 0) continue; // daca in matrix nju sunt unite
            vizi_mf[i] = true; // marchez nodul vecin
            tati[i] = nod_curent; // pun in vect de tati in dreptul n odului vecin, nodul curent
            coada_mf.push(i); // adaug vecinul in coada

        }
    }
    bool ok = vizi_mf[n]; // ok va fi dat de ultimul nod viz
    return ok;
}
void graf:: maxfl()
{
    int mflx, nod_curent;
    for(auto j: graf_mf[n]) //parc graful
    {
        if(!vizi_mf[j]) continue; // daca nodul j nu a fost viz
        mflx = capacitate[j][n]; //tinem capacitatea aferenta lui j si n in mflx
        nod_curent = j; // tinem in var nod_curent variabila j
        while(tati[nod_curent]!=0) // cat timp tatal nodului curent are atribuita o valoare
        {
            mflx = min(mflx, capacitate[tati[nod_curent]][nod_curent]); //tinem in var mflx min dintre capacit si mflx actual
            nod_curent = tati[nod_curent]; // punem in nodul curent tatal nodului curent
        }
        capacitate[j][n] = capacitate[j][n] - mflx;
        capacitate[n][j] = capacitate[n][j] + mflx;
        nod_curent = j; // ii redam nodului curent valoarea j
        while(tati[nod_curent]!=0) //reluam while-ul
        {
            capacitate[tati[nod_curent]][nod_curent] = capacitate[tati[nod_curent]][nod_curent] - mflx;
            capacitate[nod_curent][tati[nod_curent]] = capacitate[nod_curent][tati[nod_curent]] + mflx;
            nod_curent = tati[nod_curent];

        }
    }
}
void graf:: fct_mf()
{
    int rezultat = 0;
    while(bfs_mf()!=0)//cat timp se poate apela bfs_mf()
    {
        maxfl();
        memset(vizi_mf, 0, (n+1)*sizeof(bool)); //setam vizi_mf si tati de fiecare data
        memset(tati, 0, (n+1)*sizeof(int));
    }
    for(auto i: graf_mf[1]) rezultat = rezultat + capacitate[i][1];
    g << rezultat << "\n";
}

//--------maxflow---------------
//--------bellmanford------------------
void graf:: algo_bellman_ford()
{
    f >> n >> m;
    int nod1, nod2, valoare;
    vect_costuri_bellman.resize(n + 1);
    for(int i = 0; i < m; i++)
    {
        f >> nod1 >> nod2 >> valoare;
        vect_costuri_bellman[nod1].push_back(make_pair(nod2, valoare));
    }
    vector<int> distante(n + 1, INF);
    vector<int> lazy(n + 1, 0);
    queue<int> coada_bell;
    vector<bool> ok_coada_bell(n + 1, false);
    int nod_curent, nod_vecin, cost_curent;

    ok_coada_bell[1] = true; // marcam nodul de plecare ca fiind continut de coada
    distante[1] = 0; // dist de la nodul 1 la el insusi e 0
    coada_bell.push(1);

    while(!coada_bell.empty()) // cat timp coada este nevida
    {
        nod_curent = coada_bell.front(); // luam primul nod din coada
        coada_bell.pop(); // ii dam pop
        ok_coada_bell[nod_curent] = false; // il de-marcam

        for(auto it: vect_costuri_bellman[nod_curent]) // parcurgem vectorul de costuri pt nodul curent
        {
            cost_curent = it.second;
            nod_vecin = it.first;
            if(distante[nod_curent] + cost_curent < distante[nod_vecin]) // daca suma dintre distanta aferenta nodului curent + costul curent este mai mica decat dist aferenta nodului vecin
            {
                distante[nod_vecin] = distante[nod_curent] + cost_curent; // adaugam la vect de distante pt nodul vecin aceasta suma
                lazy[nod_vecin]++; // incrementam vectorul folosit drept contor pt nodul vecin
                if(lazy[nod_vecin] == n) // daca ciclul are n
                {
                    g << "Ciclu negativ!";
                    return;
                }
                if (!ok_coada_bell[nod_vecin]) // daca ok_coada_bell[nod_vecin] nu a fost vizitat
                {
                    coada_bell.push(nod_vecin); // adaugam nodul vecin in coada
                    ok_coada_bell[nod_vecin] = true; // il marcam
                }


            }
        }

    }
    for(int i = 2; i<= n; i++)
    {
          if(distante[i] == INF) g << "0 ";
          else
            g << distante[i] << " ";
    }


}
// --------------bellman-ford----------------

//---------------dijkstra-----------
void graf:: algo_dijk()
{
    int nod1, nod2, cost;
    f >> n >> m;
    vect_dijk.resize(n + 1);
    for(int i = 1; i <= m; i++)
    {
        f >> nod1 >> nod2 >> cost;
        vect_dijk[nod1].push_back(make_pair(nod2, cost));
    }
    vector<int>costx(n + 1, 100001); //vect de costuri/distante
	priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> str_djk;
	vector<bool>viz_djk(n + 1, 0); //vector vizite
	int nod_curent;
	costx[1] = 0; //dist pt nodul 1 va fi 0 initial
	str_djk.push(make_pair(0, 1));
	while (!str_djk.empty()) //cat timp pq este nevida
	{
		nod_curent = str_djk.top().second; // luam nodul din top
		str_djk.pop(); // dam pop
		if(viz_djk[nod_curent] == 0) // daca nodul extras nu a fost vizitat
		{
			viz_djk[nod_curent] = 1; // il vizitam
			for(auto it: vect_dijk[nod_curent]) // parcurgem vect_dijk pt nodul curent
			{
				if(costx[nod_curent] + it.second < costx[it.first]) //verif daca suma dintre costul aferent nodului curent si costul curent este mai mica decat costul aferent nodului vecin(it)
				{ //daca da
					costx[it.first] = costx[nod_curent] + it.second; //adunam la costul aferent nodului vecin aceasta suma
					str_djk.push(make_pair(costx[it.first], it.first)); // adaugam in pq perechea formata din costul aferent nodului vecin s, respectiv, nodul vecin
				}
			}
		}

	}
	for (int i = 2; i <= n; i++)
	{
		if(costx[i] != 100001)g << costx[i] << " "; // afisam costurile
		else
			g<<"0 ";

	}
}

//--------------dijkstra--------------
//-------------disjoint-----------------
int graf:: gaseste_radacina(int nod) // cauta radacina nodului curent
{
    if (vvect_disjoint[nod] != nod) // cat timp parintele nodului e dif de nod aplicam recursiv fct
        vvect_disjoint[nod] = gaseste_radacina(vvect_disjoint[nod]);
    return vvect_disjoint[nod]; // returnam radacina noduluji curent
}
void graf:: uneste(int nod1, int nod2)
{
    int radacina1, radacina2; // luam cele doua noduri
    radacina1 = gaseste_radacina(nod1); // le gasim punctul de plecare
    radacina2 = gaseste_radacina(nod2);
    vvect_disjoint[radacina2] = radacina1; // pastram in vvect in dreptul radacinii2 radacina1
}
void graf:: algo_disjuncte()
{
    f >> n >> m;
    for(int i = 0; i < n; i++)
        vvect_disjoint[i] = i; // pt fiecare multime punem in dreptul ei in vvect indicele i
    for(int i = 0; i < m; i++) // parc nr de operatii
    {
        int op, nod1, nod2;
        f >> op >> nod1 >> nod2;
        if(op == 1) uneste(nod1, nod2); // daca suntem pe op 1 aplicam functia uneste
        else if (op == 2)
        {
            if(gaseste_radacina(nod2) == gaseste_radacina(nod1)) // daca suntem pe op 2 verificam daca cele doua noduri date fac parte din aceeasi multime
                g << "DA" << "\n";
            else
                g << "NU" << "\n";
        }
    }
}
//----------------disjoint----------------------
//-----------------apm-----------------------
void graf :: citire_APM()
{
    f>>n>>m;
    int nod1, nod2, cost;
    vector_costuri.resize(n + 5);
    for(int i = 0; i < m; i++)
    {
        f >> nod1 >> nod2 >> cost;
        vector_costuri[nod1].push_back(make_pair(nod2, cost));
        vector_costuri[nod2].push_back(make_pair(nod1, cost));
    }

}

void graf :: algoritm_APM()
{
    priority_queue<pair<int, int>, vector<pair<int, int>>, greater<pair<int, int>>> coada_pri_APM;
    vector<int>tata(n+5, -1); // initial, vectorul de tati va contine doar -1
    vector<bool>ok_APM(n+5, 0); // ce va fi in apm este initializat cu 0
    int suma = 0;
    vector<int>costuri(n+5, 50005); // vector pt retinerea costurilor
    coada_pri_APM.push(make_pair(0, 1));
    costuri[1]=0;
    int nod_curent, cost_curent, nod_vecin;
    while(!coada_pri_APM.empty()) // cat timp avem elemente in priority queue
    {
        nod_curent = coada_pri_APM.top().second; // luma un nod din coada
        coada_pri_APM.pop(); // il extragem
        if(!ok_APM[nod_curent]) // daca modul curent nu este continut in apm
        {
            ok_APM[nod_curent] = 1; // il marcam
            for(auto it: vector_costuri[nod_curent]) //parcurgem vectorul de costuri
            {
                nod_vecin = it.first;
                cost_curent = it.second;
                if(cost_curent < costuri[nod_vecin] && !ok_APM[nod_vecin]) // daca costul curent este mai mic decat valoarea aferenta nodului vecin din vectorul de costuri si nodul vecin nu e continut in apm
                {
                    costuri[nod_vecin] = cost_curent; // valoarea corespuncatoare nodului vecin din vectorul de costuri ia valoarea costului curent
                    coada_pri_APM.push(make_pair(cost_curent, nod_vecin)); // noua pereche cost, nod
                    tata[nod_vecin] = nod_curent; // retinem in vectoul de tati, in dreptul nodului vecin, nodul curent
                }

            }
        }
    }
    for(int i = 1; i <= n; i++)
        suma = suma + costuri[i]; // parcurgem vectoruld e costuri pt a gasi suma
    g << suma << endl;
    g << n - 1 << endl;
    for(int i = 2; i <= n; i++)
        g << i << ' ' << tata[i] << endl;

}
//--------------- apm------------------
graf Gr;
int main()
{
    //BFS
/*
    int N, M, S;
    f>>N>>M>>S;
    Gr.creare_graf(N, M, S);
    Gr.creare_adiacente(M);
    Gr.bfs(S);
    for(int i = 1; i<=N; i++)
        g<< Gr.minime[i]<<" ";
*/
    //DFS
    /*
    int N, M;
    f>>N>>M;
    Gr.creare_graf_Dfs(N, M);
    Gr.creare_adiacente_Dfs(M);
    g<<Gr.comp_conexe(N);
    return 0;
*/

    //CTC
    /*
    int N, M;
    f>>N>>M;
    Gr.creare_graf_ctc(N, M);
    Gr.creare_adiacente_ctc(M);
    Gr.fct_ctc(N);
    */

    //critical connections
    /*
    int N, M;
    f>>N>>M;
    Gr.criticalConnections(N, M);
    */

    //Componente Biconexe
/*
    int N, M;
    f>>N>>M;
    Gr.creare_graf_bic(N, M);
    Gr.creare_adiacente_bic(M);
    Gr.dfs_bic(1);
    Gr.afisare_bic();
*/

    //Havel Hakimi
    /*
    vector<int>v;
    int N;
    int h;
    f>>N;
    for(int i=0; i<N; i++)
        {
            f>>h;
            v.push_back(h);
        }
{1}
    if(Gr.HavelOK(N, v)==1)
        g<<"Da";
    else
        g<<"Nu";
    */


    //Sortare Topologica
    /*
    int N, M;
    f>>N>>M;
    Gr.creare_graf_st(N, M);
    Gr.creare_adiacente_st(M);
    Gr.sortare_topologica();
    Gr.afisare_sortare_topo();
    */



    //APM
    /*
    Gr.citire_APM();
	Gr.algoritm_APM();
    */

	//Disjoint
	//Gr.algo_disjuncte();

	//Dijkstra
    //Gr.algo_dijk();

    //Bellman_ford
    //Gr.algo_bellman_ford();

    //MaxFlow
    //Gr.citire_mf();
    //Gr.fct_mf();

    //Roy-Floyd
    //Gr.citire_rf();
    //Gr.fct_royf();

    //Darb
    Gr.citire_darb();
    Gr.fct_darb();
    return 0;
}

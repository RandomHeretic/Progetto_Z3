from z3 import *
import math 


class Node:
    def __init__(self,id,f,p=False,n=False,s=False):
        self.identifier = id
        self.food = f
        self.predator = p
        self.nest = n
        self.stash = s
    def __repr__(self):
        return "identifier: " + self.identifier.__str__() + " food_value: " + self.food.__str__() + " predator_presence: " + self.predator.__str__() + " nest_presence: " + self.nest.__str__() + " "

def solve(nodes,arches,starting_energy,days,move_cap,food_cap=0,predators=False,nests=False,stashes=False):
    
    use_first_visits=False # metodo banale per la raccolta del cibo trovato, non permette la corretta implementazione delle scorte
                           #   ma più efficiente
    # solver
    s = Solver()
    
    # variabili per la serie di nodi visitati ogni giono
    Paths= [[Int(f'pos_{i}_day_{j}') for i in range(0,move_cap)] for j in range(0,days)]
    
    # variabili per la raccolta del cibo
    Food_gathered=[Int(f'food_found_on_day{n}') for n in range(0,days)]

    if use_first_visits:
        # variabili per la "prima visita"
        First_visits=[[Int(f'first_day_{n}'),Int(f'first_pos_{n}')] for n in range(1,len(nodes)+1)]
    else:
        # cibo raccolto in una data mossa di un dato giorno
        Food_gathered_pm = [[Int(f'food_found_on_day{i}_pos{j}') for j in range(0,move_cap)] for i in range(0,days)]

    # variabili per l'energia spesa
    Energy_required=[[Int(f'energy_required_on_day{n}_pos{j}-{j+1}') for j in range(0,move_cap-1)] for n in range(0,days)]
  
    # variabili per le scorte
    if stashes == True:
        Stash = []
        for n in nodes:
            if n.stash:
                Stash.append([Int(f'stash_{n.identifier}_day'),Int(f'stash_{n.identifier}_pos'),Int(f'stash_{n.identifier}_quantity'),n.identifier])


    # -- inizio impongo il nodo di partenza ha cibo uguale a 0
    for n in nodes:
        s.add(Implies(Paths[0][0]==n.identifier,n.food==0))
    s.add(Or([Paths[0][0]==n for n in range(1,len(nodes)+1)]))
    # -- fine impongo il nodo di partenza ha cibo uguale a 0

    if use_first_visits:
        # -- inizio impongo che la prima visita sia effettivamente la prima visita
        for i in range(0,len(nodes)):
            for j in range(0,days):
                for k in range(0,move_cap):
                    s.add(Implies(And(First_visits[i][0]==j,First_visits[i][1]>k),Paths[j][k]!=i+1))
                    s.add(Implies(First_visits[i][0]>j,Paths[j][k]!=i+1))
                    s.add(Implies(And(First_visits[i][0]==j,First_visits[i][1]==k),Paths[j][k]==i+1))
                    # impongo inoltre che se la prima visita di un nodo, non esiste (mai visitato) esso non venga effettivamente mai visitato
                    s.add(Implies(And(First_visits[i][0]==-1,First_visits[i][1]==-1),Paths[j][k]!=i+1))
        # -- fine impongo che la prima visita sia effettivamente la prima visita

        # -- inizio controlli per il dominio per la prima visita di un nodo
        for i in First_visits:
            s.add(And(i[1]<move_cap,i[1]>=-1))
            s.add(And(i[0]<days,i[0]>=-1))
            s.add(Implies(i[0]==-1,i[1]==-1))
            s.add(Implies(i[1]==-1,i[0]==-1))
        # -- fine controlli per il dominio per la prima visita di un nodo

    # -- inizio controllo limiti Paths

    for i in range(0,days):
        for j in range(0,move_cap):
            s.add(Or([Paths[i][j] == n for n in range(0,len(nodes)+1)]))

    # -- fine controllo limiti Paths
    

    # -- inizio imposizione che i passaggi esistano come archi o che arrivino in 0 (equivale al fermarsi per la giornata)
    for i in range(0,days):
        for j in range(0,move_cap-1):
            u = Paths[i][j]
            v = Paths[i][j+1]
            s.add(Or(Or([And(u==a[0],v==a[1]) for a in arches]),v==0))
    
    # -- fine imposizione che i passaggi esistano come archi o che arrivino in 0 (equivale al fermarsi per la giornata)

    # -- inizio contaggio energia spesa nei giorni e sue limitazioni
    for i in range(0,days):
        for j in range(0,move_cap-1):
            u = Paths[i][j]
            v = Paths[i][j+1]
            s.add([If(And(u==a[0],v==a[1]),Energy_required[i][j] == a[2],True) for a in arches])
            s.add(Or(Or([Energy_required[i][j]==a[2] for a in arches]),Energy_required[i][j]==0))
            s.add(Implies(v==0,Energy_required[i][j]==0))
    # -- fine contaggio energia spesa nei giorni e sue limitazioni

    # -- inizio contaggio cibo trovato e sue limitazioni
    
    for i in range(0,days):
        if use_first_visits:
            s.add(Food_gathered[i] == Sum([If(First_visits[n][0]==i,nodes[n].food,0)for n in range(0,len(nodes))]))
        else:    
            if stashes==False:
                s.add(Food_gathered[i] == Sum(Food_gathered_pm[i]))
            elif stashes==True:
                s.add(Food_gathered[i] == Sum(Food_gathered_pm[i]) - Sum([If(k[0]==i,k[2],0) for k in Stash]))


    if not use_first_visits:
        if stashes==False:
            for i in range(0,days):
                s.add(Food_gathered_pm[i][0]==0)
                for j in range(0,move_cap):
                    s.add(Food_gathered_pm[i][j]>=0)
                    s.add([If(Paths[i][j]==n,Food_gathered_pm[i][j]<=nodes[n-1].food-Sum([If(Paths[math.floor(k/move_cap)][k%move_cap]==n,Food_gathered_pm[math.floor(k/move_cap)][k%move_cap],0) for k in range(0,(i*move_cap)+j)]),True) for n in range(1,len(nodes)+1)])
                    s.add(Implies(Paths[i][j]==0,Food_gathered_pm[i][j]==0))
        elif stashes==True:
            for i in range(0,days):
                s.add(Food_gathered_pm[i][0]==0)
                for j in range(0,move_cap):
                    s.add(Food_gathered_pm[i][j]>=0)
                    s.add([If(Paths[i][j]==n,Food_gathered_pm[i][j]<=nodes[n-1].food + Sum([If(And(Stash[k][3]==n,(Stash[k][0]+1)<i),Stash[k][2],0)for k in range(0,len(Stash))]) - Sum([If(Paths[math.floor(k/move_cap)][k%move_cap]==n,Food_gathered_pm[math.floor(k/move_cap)][k%move_cap],0) for k in range(0,(i*move_cap)+j)]),True) for n in range(1,len(nodes)+1)])
                    s.add(Implies(Paths[i][j]==0,Food_gathered_pm[i][j]==0))

    # -- fine contaggio cibo trovato e sue limitazioni


    # -- inizio imposizione che se smetto di muovermi non mi muovo 
    for i in range(0,days):
        for j in range(0,move_cap-1):
            s.add(Implies(Paths[i][j]==0,Paths[i][j+1]==0)) 
    # -- fine imposizione che se smetto di muovermi non mi muovo 
    
    # -- inizio controllo sufficiente cibo
    s.add(Sum(Energy_required[0])<=starting_energy)
    s.add(Food_gathered[0]>0)
    for i in range(1,days):
        s.add(Food_gathered[i]>0)
        s.add(Sum(Energy_required[i])<=Food_gathered[i-1])
    # -- fine controllo sufficiente cibo 
    
    # -- inizio controllo ultima posizione uguale alla prima del nuovo giorno
    for i in range(0,days-1):
        for j in range(0,move_cap-1):
            u = Paths[i][j]
            v = Paths[i][j+1]
            s.add(Implies(And(v==0,u!=0),Paths[i+1][0]==u))
        s.add(Implies(Paths[i][move_cap-1]!=0,Paths[i+1][0]==Paths[i][move_cap-1]))
    # -- fine controllo ultima posizione uguale alla prima del nuovo giorno
    
    # -- inizio imposizione cap del cibo

    if food_cap!=0:
        for i in range(0,days):
            s.add(Food_gathered[i]<=food_cap)

    # -- fine imposizione cap del cibo


    # -- inizio controllo predatori
    if predators==True and nests==False:
        for i in range(0,days):
            for j in range(0,move_cap-1):
                u = Paths[i][j]
                v = Paths[i][j+1]
                s.add([Implies(And(v==0,u!=0),If(n.predator,u!=n.identifier,True)) for n in nodes])
            s.add([Implies(Paths[i][move_cap-1]!=0,If(n.predator,Paths[i][move_cap-1]!=n.identifier,True))for n in nodes])
    # -- fine controllo predatori

    # -- inizio controllo nidi
    if nests==True:
        for i in range(0,days):
            for j in range(0,move_cap-1):
                u = Paths[i][j]
                v = Paths[i][j+1]
                s.add([Implies(And(v==0,u!=0),If(n.nest,True,u!=n.identifier)) for n in nodes])
            s.add([Implies(Paths[i][move_cap-1]!=0,If(n.nest,True,Paths[i][move_cap-1]!=n.identifier))for n in nodes])
    # -- fine controllo nidi

    # -- inizio controllo scorte
    if stashes==True:
        for i in Stash:
            s.add(And(i[0]>=-1,i[0]<days))
            s.add(And(i[1]>=-1,i[1]<move_cap))
            s.add(i[2]>=0)
            s.add(Implies(i[0]==-1,i[1]==-1))
            s.add(Implies(i[1]==-1,i[0]==-1))
            s.add(Implies(i[0]==-1,i[2]==0))
            s.add(Implies(i[2]==0,i[0]==-1))
            for j in range(0,days):
                for k in range(0,move_cap):
                    s.add(Implies(And(i[0]==j,i[1]==k),Paths[j][k]==i[3]))
            s.add(i[2]==Sum([If(i[0]==j,Sum([If(i[1]>=k,Food_gathered_pm[j][k],0) for k in range(0,move_cap)]),0) for j in range(0,days)])/2)
    # -- fine controllo scorte

    # stampo infomazioni
    print(s.check())
    if s.check().__str__() == "unsat":
        return
    dump = s.model()
    err =[]
    food_control = []
    data=[]
    for i in range(0,days):
        for j in range(0,move_cap):
            data.append(dump.eval(Paths[i][j]))
        data.append('-')
        food_control.append(dump.eval(Food_gathered[i]).as_long())
        data.append(food_control[i])
        if food_control[i] <= 0:
            err.append(f'no food on day {i}') # errore di assenza di cibo nel giorno i
        print(data)
        data = []
        for j in range(0,move_cap):
            data.append(dump.eval(Food_gathered_pm[i][j]).as_long())
        print(" ",data)
        data = []
    print()
    data = []
    for i in range(0,days):
        for j in range(0,move_cap-1):
            data.append(dump.eval(Energy_required[i][j]).as_long())
        if i==0:
            if starting_energy < sum(data):
                err.append("too little energy on day 0") # errore di consumo di energia
        elif sum(data) > food_control[i-1]:
            err.append(f'too little food on day {i-1}') # errore di consumo di energia
        print(data)
        data = []
    if use_first_visits:
        for i in range(0,len(nodes)):
            data.append([i+1,dump.eval(First_visits[i][0]).as_long(),dump.eval(First_visits[i][1]).as_long()])
        for node in data:
            for i in range(0,node[1]+1):
                for j in range(0,move_cap):
                    if node[1] != i:
                        if dump.eval(Paths[i][j]).as_long() == node[0]:
                            err.append("errore a " + node[0].__str__()) # errore first visit
                    elif node[2] > j:
                        if dump.eval(Paths[i][j]).as_long() == node[0]:
                            err.append("errore a " + node[0].__str__()) # errore first visit
        print(data)
    for node in nodes:
        if node.predator and predators:
            for i in range(0,days):
                for j in range(0,move_cap-1):
                    u = dump.eval(Paths[i][j]).as_long()
                    v = dump.eval(Paths[i][j+1]).as_long()
                    if v==0 and u==node.identifier and not(node.nest):
                        err.append(f'day {i} ended on a predator')
                if dump.eval(Paths[i][move_cap-1]).as_long() == node.identifier and not(node.nest):
                    err.append(f'day {i} ended on a predator')
        if not(node.nest) and nests:
            for i in range(0,days):
                for j in range(0,move_cap-1):
                    u = dump.eval(Paths[i][j]).as_long()
                    v = dump.eval(Paths[i][j+1]).as_long()
                    if v==0 and u==node.identifier:
                        err.append(f'day {i} not ended on a nest')
                if dump.eval(Paths[i][move_cap-1]).as_long() == node.identifier:
                    err.append(f'day {i} not ended on a nest')
    data=[]
    if stashes==True:
        for i in Stash:
            buff = [i[3],dump.eval(i[0]).as_long(),dump.eval(i[1]).as_long(),dump.eval(i[2]).as_long()]
            data.append(buff)
        print(data)
    if len(err)!=0:
        print("errori:")
        print(err)
    
        
    


#test 1 -- base base
nodes=[(1,1),(2,0)]
Nnodes=[]
for i in nodes:
    Nnodes.append(Node(i[0],i[1]))
arches=[[2,1,2]]
days=1
energy=3
move_cap=5
print("test 1:")
solve(Nnodes,arches,energy,days,move_cap)
print()

# test 2 -- mid
nodes = [(1,0),(2,1),(3,7),(4,3),(5,12)]
Nnodes = []
for i in nodes:
    Nnodes.append(Node(i[0],i[1]))
arches = [[1,2,3],[2,1,1],[1,4,8],[4,3,5],[2,5,3],[5,3,8]]
days = 2
energy = 10
move_cap = 10
print("test 2:")
solve(Nnodes,arches,energy,days,move_cap)
print()

#test 3 -- mid
nodes = [(1,0),(2,5),(3,1),(4,8),(5,86),(6,0),(7,5)]
Nnodes = []
for i in nodes:
    Nnodes.append(Node(i[0],i[1]))
arches = [[1,5,9],[3,7,6],[2,4,5],[2,1,4],[6,2,1],[7,5,2]]
print("test 3:")
solve(Nnodes,arches,5,2,5)
print()

#test 4 -- test food_cap
nodes = [(1,0),(2,5),(3,5),(4,8),(5,86),(6,0),(7,5)]
Nnodes = []
for i in nodes:
    Nnodes.append(Node(i[0],i[1]))
arches = [[1,5,1],[3,7,2],[2,4,3],[2,1,4],[6,2,1],[7,5,2],[1,6,1],[6,1,1],[1,7,3]]
print("test 4:")
solve(Nnodes,arches,5,2,5,10)
print()

#test 5 -- test predatori no nidi
nodes = [(1,0,False),(2,1,False),(3,7,False),(4,3,False),(5,12,True)]
Nnodes = []
for i in nodes:
    Nnodes.append(Node(i[0],i[1],i[2]))
arches = [[1,2,3],[2,1,1],[1,4,8],[4,3,5],[2,5,3],[5,3,8],[5,1,4]]
days = 2
energy = 10
move_cap = 10
print("test 5:")
solve(Nnodes,arches,energy,days,move_cap,0,True)
print()

#test 6 -- test nidi no predatori
nodes = [(1,0,False,True),(2,1,False,False),(3,7,False,True),(4,3,False,False),(5,12,False,False)]
Nnodes = []
for i in nodes:
    Nnodes.append(Node(i[0],i[1],i[2],i[3]))
arches = [[1,2,3],[2,1,1],[1,4,8],[4,3,5],[2,5,3],[5,3,8],[5,1,4]]
days = 2
energy = 10
move_cap = 10
print("test 6:")
solve(Nnodes,arches,energy,days,move_cap,0,False,True)
print()

#test 7 -- test sia nidi che predatori
nodes = [(1,0,True,True),(2,1,False,False),(3,7,False,False),(4,3,False,False),(5,12,True,False)]
Nnodes = []
for i in nodes:
    Nnodes.append(Node(i[0],i[1],i[2],i[3]))
arches = [[1,2,3],[2,1,1],[1,4,8],[4,3,4],[2,5,3],[5,3,8],[5,1,4],[3,1,1]]
days = 2
energy = 10
move_cap = 10
print("test 7:")
solve(Nnodes,arches,energy,days,move_cap,0,True,True)
print()

#test 8 -- test scorte
nodes = [(1,0,True,True,False),(2,10,False,False,True),(3,7,False,False,False),(4,3,False,False,False),(5,12,True,False,False)]
Nnodes = []
for i in nodes:
    Nnodes.append(Node(i[0],i[1],i[2],i[3],i[4]))
arches = [[1,2,3],[2,1,1],[1,4,8],[4,3,4],[2,5,3],[5,3,8],[5,1,4],[3,1,1]]
days = 5
energy = 10
move_cap = 10
print("test 8:")
solve(Nnodes,arches,energy,days,move_cap,0,False,False,True)
print()

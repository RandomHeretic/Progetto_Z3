# Progetto_Z3
Il problema di seguito presentato è la mia proposta per il progetto in Z3 in alternativa all’esame orale del corso di computabilità, complessità e logica insegnato dal prof. Peron Adriano.


Vogliamo determinare se la sopravvivenza di un animale su n giorni in uno spazio predeterminato con le seguenti assunzioni:

-L’animale comincia il primo giorno con una quantità di energia “e” predeterminata dal problema

-Lo spazio dove l’animale si può muovere è rappresentato con un grafo pesato con un numero naturale “k” assegnato a ciascun nodo. Ogni nodo rappresenta un luogo di interesse per l’animale che contiene una quantità “k” di cibo, il peso degli archi è la quantità di energia necessaria per attraversarlo. Per costruzione richiediamo che almeno un nodo abbia “k=0”

-L’unico modo di passare da un nodo ad un’altro è attraverso gli archi dati

-Per attraversare un arco con peso “w” l’animale necessita di avere energia “e” maggiore o uguale a “w”, dopo l’aver attraversato l’arco all’animale rimarrà “e - w” energia

-L’animale può partire da un qualunque nodo a cui è assegnato uno “0”

-In un giorno, l’animale non ha limiti di archi che può attraversare e non ha limiti di quanto cibo può raccogliere

-L’animale decide quando fermarsi per terminare il giorno corrente e cominciare il giorno successivo

-Alla terminazione di un giorno l’energia rimasta all’animale viene annullata e comincia il giorno successivo con un quantitativo di energia pari alle unità di cibo che ha trovato nel giorno precedente.

-Se al termine di un giorno l’animale termina senza l’aver trovato cibo allora l’animale “muore” e la simulazione fallisce

-Se è possibile ottenere uno scenario dove l’animale sopravvive per tutti gli “n” giorni vogliamo trovare il percorso compiuto e i momenti in cui l’animale decide di terminare le sue giornate

-Se non è possibile trovare un percorso come richiesto dal punto precedente allora diciamo che il problema è insoddisfacibile per il grafo dato in “n” giorni

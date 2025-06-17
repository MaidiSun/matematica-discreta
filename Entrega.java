import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;
import java.util.function.BiFunction;
import java.util.function.BiPredicate;
import java.util.function.BooleanSupplier;
import java.util.function.Function;
import java.util.function.Predicate;
import java.util.stream.IntStream;

/*
 * Aquesta entrega consisteix en implementar tots els mètodes anomenats "exerciciX". Ara mateix la
 * seva implementació consisteix en llançar `UnsupportedOperationException`, ho heu de canviar així
 * com els aneu fent.
 *
 * Criteris d'avaluació:
 *
 * - Si el codi no compila tendreu un 0.
 *
 * - Les úniques modificacions que podeu fer al codi són:
 *    + Afegir un mètode (dins el tema que el necessiteu)
 *    + Afegir proves a un mètode "tests()"
 *    + Òbviament, implementar els mètodes que heu d'implementar ("exerciciX")
 *   Si feu una modificació que no sigui d'aquesta llista, tendreu un 0.
 *
 * - Principalment, la nota dependrà del correcte funcionament dels mètodes implementats (provant
 *   amb diferents entrades).
 *
 * - Tendrem en compte la neteja i organització del codi. Un estandard que podeu seguir és la guia
 *   d'estil de Google per Java: https://google.github.io/styleguide/javaguide.html . Per exemple:
 *    + IMPORTANT: Aquesta entrega està codificada amb UTF-8 i finals de línia LF.
 *    + Indentació i espaiat consistent
 *    + Bona nomenclatura de variables
 *    + Declarar les variables el més aprop possible al primer ús (és a dir, evitau blocs de
 *      declaracions).
 *    + Convé utilitzar el for-each (for (int x : ...)) enlloc del clàssic (for (int i = 0; ...))
 *      sempre que no necessiteu l'índex del recorregut. Igualment per while si no és necessari.
 *
 * Per com està plantejada aquesta entrega, no necessitau (ni podeu) utilitzar cap `import`
 * addicional, ni qualificar classes que no estiguin ja importades. El que sí podeu fer és definir
 * tots els mètodes addicionals que volgueu (de manera ordenada i dins el tema que pertoqui).
 *
 * Podeu fer aquesta entrega en grups de com a màxim 3 persones, i necessitareu com a minim Java 10.
 * Per entregar, posau els noms i cognoms de tots els membres del grup a l'array `Entrega.NOMS` que
 * està definit a la línia 53.
 *
 * L'entrega es farà a través d'una tasca a l'Aula Digital que obrirem abans de la data que se us
 * hagui comunicat. Si no podeu visualitzar bé algun enunciat, assegurau-vos de que el vostre editor
 * de texte estigui configurat amb codificació UTF-8.
 */
class Entrega {

    static final String[] NOMS = {"Maidi Sun", "Daniel Martín Colomar", "Alberto Atero García"};

    /*
   * Aquí teniu els exercicis del Tema 1 (Lògica).
     */
    static class Tema1 {
    /*
     * Determinau si l'expressió és una tautologia o no:
     *
     * (((vars[0] ops[0] vars[1]) ops[1] vars[2]) ops[2] vars[3]) ...
     *
     * Aquí, vars.length == ops.length+1, i cap dels dos arrays és buid. Podeu suposar que els
     * identificadors de les variables van de 0 a N-1, i tenim N variables diferents (mai més de 20
     * variables).
     *
     * Cada ops[i] pot ser: CONJ, DISJ, IMPL, NAND.
     *
     * Retornau:
     *   1 si és una tautologia
     *   0 si és una contradicció
     *   -1 en qualsevol altre cas.
     *
     * Vegeu els tests per exemples.
     */
    static final char CONJ = '∧';
    static final char DISJ = '∨';
    static final char IMPL = '→';
    static final char NAND = '.';


        static int exercici1(char[] ops, int[] vars) {
            int n = vars.length;
            int numVars = n + 1; // numero de variables

            // generamos todas las combinacionees posibles de valores para las Variables
            int totalCombinaciones = 1 << numVars; // 2^n combinaciones
            boolean esTautologia = true;
            boolean esContradiccion = true;

            // evaluamos para cada combinacion de valores de las variables
            for (int i = 0; i < totalCombinaciones; i++) {
                boolean[] valVars = new boolean[numVars];

                // asignamos los valores de las variables segun la combinacion
                for (int j = 0; j < numVars; j++) {
                    valVars[j] = (i & (1 << j)) != 0; // usa mascara de bits para saber el valor de cada var
                }

                // evaluamos la expresion booleana con los valoress asignados
                boolean resultado = valVars[vars[0]];
                for (int j = 0; j < ops.length; j++) {
                    boolean v1 = resultado;
                    boolean v2 = valVars[vars[j + 1]];

                    // aplicamos el operador correspondiente
                    switch (ops[j]) {
                        case CONJ:
                            resultado = v1 && v2;
                            break;
                        case DISJ:
                            resultado = v1 || v2;
                            break;
                        case IMPL:
                            resultado = !v1 || v2;
                            break;
                        case NAND:
                            resultado = !(v1 && v2);
                            break;
                    }
                }

                // actualizamos si la expresioon es una tautologia o contradiccio
                if (resultado) {
                    esContradiccion = false;
                } else {
                    esTautologia = false;
                }
            }

            // determinamos el tipoo de expresion
            if (esTautologia) {
                return 1; // tautología
            } else if (esContradiccion) {
                return 0; // contradiccion
            } else {
                return -1; // ni tautologia ni contradicción
            }
        }

    /*
     * Aquest mètode té de paràmetre l'univers (representat com un array) i els predicats
     * adients `p` i `q`. Per avaluar aquest predicat, si `x` és un element de l'univers, podeu
     * fer-ho com `p.test(x)`, que té com resultat un booleà (true si `P(x)` és cert).
     *
     * Amb l'univers i els predicats `p` i `q` donats, returnau true si la següent proposició és
     * certa.
     *
     * (∀x : P(x)) <-> (∃!x : Q(x))
     */
        static boolean exercici2(int[] universe, Predicate<Integer> p, Predicate<Integer> q) {
            // comprobamaos si p(x) es cierto per a tot element de l'univers
            boolean todosCumplenP = true;
            for (int i = 0; i < universe.length; i++) {
                int valor = universe[i];
                if (!p.test(valor)) {
                    todosCumplenP = false;
                    break;
                }
            }

            // comprobamos si existe exactament 1 element x tal q Q(x) sea cierto
            int cantidadQueCumplenQ = 0;
            for (int i = 0; i < universe.length; i++) {
                int valor = universe[i];
                if (q.test(valor)) {
                    cantidadQueCumplenQ++;
                    if (cantidadQueCumplenQ > 1) {
                        // si hay mas d un elemento que cumple Q(x), devolvemos false
                        return false;
                    }
                }
            }

            // verificamos si la propocisión es cierta: 
            // para todos x se cumple p(x) sii existe unico x q cumple q(x)
            return (todosCumplenP == (cantidadQueCumplenQ == 1));
        }

        static void tests() {
          // Exercici 1
          // Taules de veritat

          // Tautologia: ((p0 → p2) ∨ p1) ∨ p0
          test(1, 1, 1, () -> exercici1(new char[] { IMPL, DISJ, DISJ }, new int[] { 0, 2, 1, 0 }) == 1);

          // Contradicció: (p0 . p0) ∧ p0
          test(1, 1, 2, () -> exercici1(new char[] { NAND, CONJ }, new int[] { 0, 0, 0 }) == 0);

          // Exercici 2
          // Equivalència

          test(1, 2, 1, () -> {
            return exercici2(new int[] { 1, 2, 3 }, (x) -> x == 0, (x) -> x == 0);
          });

          test(1, 2, 2, () -> {
            return exercici2(new int[] { 1, 2, 3 }, (x) -> x >= 1, (x) -> x % 2 == 0);
          });
        }
    }

    /*
   * Aquí teniu els exercicis del Tema 2 (Conjunts).
   *
   * Per senzillesa tractarem els conjunts com arrays (sense elements repetits). Per tant, un
   * conjunt de conjunts d'enters tendrà tipus int[][]. Podeu donar per suposat que tots els
   * arrays que representin conjunts i us venguin per paràmetre estan ordenats de menor a major.
   *
   * Les relacions també les representarem com arrays de dues dimensions, on la segona dimensió
   * només té dos elements. L'array estarà ordenat lexicogràficament. Per exemple
   *   int[][] rel = {{0,0}, {0,1}, {1,1}, {2,2}};
   * i també donarem el conjunt on està definida, per exemple
   *   int[] a = {0,1,2};
   * Als tests utilitzarem extensivament la funció generateRel definida al final (també la podeu
   * utilitzar si la necessitau).
   *
   * Les funcions f : A -> B (on A i B son subconjunts dels enters) les representam o bé amb el seu
   * graf o bé amb un objecte de tipus Function<Integer, Integer>. Sempre donarem el domini int[] a
   * i el codomini int[] b. En el cas de tenir un objecte de tipus Function<Integer, Integer>, per
   * aplicar f a x, és a dir, "f(x)" on x és d'A i el resultat f.apply(x) és de B, s'escriu
   * f.apply(x).
     */
    static class Tema2 {
    /*
     * Trobau el nombre de particions diferents del conjunt `a`, que podeu suposar que no és buid.
     *
     * Pista: Cercau informació sobre els nombres de Stirling.
     */
    static int exercici1(int[] a) {
       int n = a.length;  // tamaño del conjnto a

            // creamos una tabla para guardar los numeross de Stirling 
            int[][] stirling = new int[n + 1][n + 1];

            // inicializamoos las condiciones base
            stirling[0][0] = 1;

            // calculo de los numeros de stirling de segundo orden S(n, k)
            for (int i = 1; i <= n; i++) {
                for (int k = 1; k <= i; k++) {
                    stirling[i][k] = k * stirling[i - 1][k] + stirling[i - 1][k - 1];
                }
            }

            // la suma total de particiones distintas es sumar S(n,k) de k=1 a n
            int totalParticiones = 0;
            for (int k = 1; k <= n; k++) {
                totalParticiones += stirling[n][k];
            }

            return totalParticiones; // devolvemos el total d particiones
        }

        /*
     * Trobau el cardinal de la relació d'ordre parcial sobre `a` més petita que conté `rel` (si
     * existeix). En altres paraules, el cardinal de la seva clausura reflexiva, transitiva i
     * antisimètrica.
     *
     * Si no existeix, retornau -1.
         */
    static int exercici2(int[] a, int[][] rel) {
       int n = a.length;  // numero de elemntos en el conjunto

            // inicializar la matriz de relación de tamaño n x n
            int[][] relacion = new int[n][n];

            // convertimos la relación dada en una matris de relacion
            for (int[] par : rel) {
                int x = par[0];
                int y = par[1];

                // si ya hay la relacion inversa (x,y) y (y,x) con x != y, no se puede construir una relacion antisimetrica
                if (x != y && relacion[y][x] == 1) {
                    return -1;  // violación de antisimetria
                }

                relacion[x][y] = 1;  // (x, y) está en la relazion
            }

            // añadimos reflexividad: (x,x) debe estar siempre en la relacion
            for (int i = 0; i < n; i++) {
                relacion[i][i] = 1;
            }

            // añadimos transitividad: si (x,y) y (y,z) existen, añadimos (x,z)
            boolean cambio = true;
            while (cambio) {
                cambio = false;
                for (int i = 0; i < n; i++) {
                    for (int j = 0; j < n; j++) {
                        if (relacion[i][j] == 1) {
                            for (int k = 0; k < n; k++) {
                                if (relacion[j][k] == 1 && relacion[i][k] == 0) {
                                    relacion[i][k] = 1;  // añadimmos la transitividad
                                    cambio = true;
                                }
                            }
                        }
                    }
                }
            }

            // añadimos antisimetria: si (x,y) y (y,x) existen y x != y, quitamos una de las dos
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    if (i != j && relacion[i][j] == 1 && relacion[j][i] == 1) {
                        relacion[i][j] = 0;  // eliminamos (i,j) para que sea antisimetrico
                    }
                }
            }

            // calculamos el cardinal de la relación de orden parcial
            int cardinal = 0;
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < n; j++) {
                    if (relacion[i][j] == 1) {
                        cardinal++;
                    }
                }
            }

            return cardinal;
        }


        /*
     * Donada una relació d'ordre parcial `rel` definida sobre `a` i un subconjunt `x` de `a`,
     * retornau:
     * - L'ínfim de `x` si existeix i `op` és false
     * - El suprem de `x` si existeix i `op` és true
     * - null en qualsevol altre cas
         */
        static Integer exercici3(int[] a, int[][] rel, int[] x, boolean op) {
           
            Integer resultado = null;

            // si op es false, buscamos el infimo de x
            if (!op) {
                for (int posibleElemento : a) {
                    boolean esInfimo = true;
                    // comprovamos si el candidato es menor o igual q todos los elemntos de x segun la relacion
                    for (int elemento : x) {
                        boolean relacionado = false;
                        for (int[] par : rel) {
                            if (par[0] == posibleElemento && par[1] == elemento) {
                                relacionado = true;
                                break;
                            }
                        }
                        if (!relacionado) {
                            esInfimo = false;
                            break;
                        }
                    }
                    // si encontramos un candidato que es el infimo de x, lo actualizamos
                    if (esInfimo) {
                        if (resultado == null) {
                            resultado = posibleElemento;
                        } else {
                            boolean esMasGrande = false;
                            for (int[] par : rel) {
                                if (par[0] == resultado && par[1] == posibleElemento) {
                                    esMasGrande = true;
                                    break;
                                }
                            }
                            if (!esMasGrande) {
                                resultado = posibleElemento;
                            }
                        }
                    }
                }
            } // si op es true, buscamos el supremoo de x
            else {
                for (int candidato : a) {
                    boolean esSuprem = true;
                    // revisamos si el candidato es mayor o igual a todos los elementos de x segun la relazion
                    for (int element : x) {
                        boolean relacionado = false;
                        for (int[] par : rel) {
                            if (par[0] == element && par[1] == candidato) {
                                relacionado = true;
                                break;
                            }
                        }
                        if (!relacionado) {
                            esSuprem = false;
                            break;
                        }
                    }
                    // si vemos que el candidato es el supremo, actualizamos
                    if (esSuprem) {
                        if (resultado == null) {
                            resultado = candidato;
                        } else {
                            boolean esMasPeque = false;
                            for (int[] par : rel) {
                                if (par[0] == candidato && par[1] == resultado) {
                                    esMasPeque = true;
                                    break;
                                }
                            }
                            if (!esMasPeque) {
                                resultado = candidato;
                            }
                        }
                    }
                }
            }

            return resultado;
        }


        /*
     * Donada una funció `f` de `a` a `b`, retornau:
     *  - El graf de la seva inversa (si existeix)
     *  - Sinó, el graf d'una inversa seva per l'esquerra (si existeix)
     *  - Sinó, el graf d'una inversa seva per la dreta (si existeix)
     *  - Sinó, null.
         */
        static int[][] exercici4(int[] a, int[] b, Function<Integer, Integer> f) {
            int tamanoA = a.length;
            int tamanoB = b.length;
    
    // creamos una lista donde cada posición tiene los valores de a que se asignan a un valor de b 
    List<List<Integer>> preimagenes = new ArrayList<>();
    for (int i = 0; i < tamanoB; i++) {
        preimagenes.add(new ArrayList<>());
    }
    
    // rellenamos las listas de preimagenes
    for (int i = 0; i < tamanoA; i++) {
        int x = a[i];
        int y = f.apply(x);
        
        // encontramos el indice de y en b
        int indiceY = -1;
        for (int j = 0; j < tamanoB; j++) {
            if (b[j] == y) {
                indiceY = j;
                break;
            }
        }
        
        if (indiceY != -1) {
            preimagenes.get(indiceY).add(x);
        }
    }

    // verificar si la funcion es inyectiva , es decir, que no haya valores repetidos en lista prepiamgenes
    boolean inyectiva = true;
    for (int i = 0; i < tamanoB; i++) {
        if (preimagenes.get(i).size() > 1) {
            inyectiva = false;
            break;
        }
    }

    // verificar si la funciin es sobreyectiva , es decir, que todlos los valores d eB esten cubiertos
    boolean sobreyectiva = true;
    for (int i = 0; i < tamanoB; i++) {
        if (preimagenes.get(i).isEmpty()) {
            sobreyectiva = false;
            break;
        }
    }

    // si la función es bijectiva, podemos devolver la inversa
    if (inyectiva && sobreyectiva) {
        int[][] grafoInverso = new int[tamanoB][2];
        for (int i = 0; i < tamanoB; i++) {
            int y = b[i];
            int x = preimagenes.get(i).get(0);  // solo un valor de x
            grafoInverso[i][0] = y;
            grafoInverso[i][1] = x;
        }
        return grafoInverso;
    }

    // si es inyectiva, devolvemos la inversa por la izquierda
    if (inyectiva) {
        int[][] grafoInversoIzq = new int[tamanoB][2];
        for (int i = 0; i < tamanoB; i++) {
            int y = b[i];
            if (!preimagenes.get(i).isEmpty()) {
                int x = preimagenes.get(i).get(0);
                grafoInversoIzq[i][0] = y;
                grafoInversoIzq[i][1] = x;
            } else {
                grafoInversoIzq[i][0] = y;
                grafoInversoIzq[i][1] = y;  // identidad
            }
        }
        return grafoInversoIzq;
    }

    // si es sobreyectiva, devolvemos la inversa por la derecha
    if (sobreyectiva) {
        int[][] inversoGrafoDcho = new int[tamanoB][2];
        for (int i = 0; i < tamanoB; i++) {
            int y = b[i];
            List<Integer> lista = preimagenes.get(i);
            // elegir el valor mínimo de x
            int minX = lista.get(0);
            for (int j = 1; j < lista.size(); j++) {
                if (lista.get(j) < minX) {
                    minX = lista.get(j);
                }
            }
            inversoGrafoDcho[i][0] = y;
            inversoGrafoDcho[i][1] = minX;
        }
        return inversoGrafoDcho;
    }

    // si no existe ninguna de las inversas  devolvermos null
    return null;

        }

        /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
         */
        static void tests() {
            // Exercici 1
            // Nombre de particions

            test(2, 1, 1, () -> exercici1(new int[]{1}) == 1);
            test(2, 1, 2, () -> exercici1(new int[]{1, 2, 3}) == 5);

            // Exercici 2
            // Clausura d'ordre parcial
            final int[] INT02 = {0, 1, 2};

            test(2, 2, 1, () -> exercici2(INT02, new int[][]{{0, 1}, {1, 2}}) == 6);
            test(2, 2, 2, () -> exercici2(INT02, new int[][]{{0, 1}, {1, 0}, {1, 2}}) == -1);

            // Exercici 3
            // Ínfims i suprems
            final int[] INT15 = {1, 2, 3, 4, 5};
            final int[][] DIV15 = generateRel(INT15, (n, m) -> m % n == 0);
            final Integer ONE = 1;

            test(2, 3, 1, () -> ONE.equals(exercici3(INT15, DIV15, new int[]{2, 3}, false)));
            test(2, 3, 2, () -> exercici3(INT15, DIV15, new int[]{2, 3}, true) == null);

            // Exercici 4
            // Inverses
            final int[] INT05 = {0, 1, 2, 3, 4, 5};

            test(2, 4, 1, () -> {
                var inv = exercici4(INT05, INT02, (x) -> x / 2);

                if (inv == null) {
                    return false;
                }

                inv = lexSorted(inv);

                if (inv.length != INT02.length) {
                    return false;
                }

                for (int i = 0; i < INT02.length; i++) {
                    if (inv[i][0] != i || inv[i][1] / 2 != i) {
                        return false;
                    }
                }

                return true;
            });

            test(2, 4, 2, () -> {
                var inv = exercici4(INT02, INT05, (x) -> x);

                if (inv == null) {
                    return false;
                }

                inv = lexSorted(inv);

                if (inv.length != INT05.length) {
                    return false;
                }

                for (int i = 0; i < INT02.length; i++) {
                    if (inv[i][0] != i || inv[i][1] != i) {
                        return false;
                    }
                }

                return true;
            });
        }

        /*
     * Ordena lexicogràficament un array de 2 dimensions
     * Per exemple:
     *  arr = {{1,0}, {2,2}, {0,1}}
     *  resultat = {{0,1}, {1,0}, {2,2}}
         */
        static int[][] lexSorted(int[][] arr) {
            if (arr == null) {
                return null;
            }

            var arr2 = Arrays.copyOf(arr, arr.length);
            Arrays.sort(arr2, Arrays::compare);
            return arr2;
        }

        /*
     * Genera un array int[][] amb els elements {a, b} (a de as, b de bs) que satisfàn pred.test(a, b)
     * Per exemple:
     *   as = {0, 1}
     *   bs = {0, 1, 2}
     *   pred = (a, b) -> a == b
     *   resultat = {{0,0}, {1,1}}
         */
        static int[][] generateRel(int[] as, int[] bs, BiPredicate<Integer, Integer> pred) {
            var rel = new ArrayList<int[]>();

            for (int a : as) {
                for (int b : bs) {
                    if (pred.test(a, b)) {
                        rel.add(new int[]{a, b});
                    }
                }
            }

            return rel.toArray(new int[][]{});
        }

        // Especialització de generateRel per as = bs
        static int[][] generateRel(int[] as, BiPredicate<Integer, Integer> pred) {
            return generateRel(as, as, pred);
        }
    }

    /*
   * Aquí teniu els exercicis del Tema 3 (Grafs).
   *
   * Els (di)grafs vendran donats com llistes d'adjacència (és a dir, tractau-los com diccionaris
   * d'adjacència on l'índex és la clau i els vèrtexos estan numerats de 0 a n-1). Per exemple,
   * podem donar el graf cicle no dirigit d'ordre 3 com:
   *
   * int[][] c3dict = {
   *   {1, 2}, // veïns de 0
   *   {0, 2}, // veïns de 1
   *   {0, 1}  // veïns de 2
   * };
     */
    static class Tema3 {

        /*
     * Determinau si el graf `g` (no dirigit) té cicles.
         */
        static boolean exercici1(int[][] g) {
            // obtiene el número de vértices en el grafo 'g'
            int n = g.length;

            // crea una lista booleana para marcar los vertices visitados durante la búsqueda
            boolean[] visitat = new boolean[n];

            // recorre todos los vertices del grafo
            for (int v = 0; v < n; v++) {
                if (!visitat[v]) { // Si el vértice 'v' no ha sido visitado aun
                    // Realiza una búsqueda en profundidad (DFS) para detectar un ciclo
                    // dfsCiclo recibe el grafo, el vértice actual, el vértice raiz (-1 indica que no tiene padre) y la lista de visitados
                    if (dfsCiclo(g, v, -1, visitat)) {
                        // Si se detecta un ciclo, devuelve true
                        return true;
                    }
                }
            }

            // Si no se detectaron ciclos en ninguna componente del grafo, devuelve false
            return false;

        }

        static boolean dfsCiclo(int[][] g, int actual, int raiz, boolean[] visitado) {
            visitado[actual] = true; // Marcamos el vertice actual como visistado

            for (int vecino : g[actual]) {
                if (!visitado[vecino]) {
                    // Si el vecino no ha sido visitado, hacemos una llamada recursiva al DFS
                    if (dfsCiclo(g, vecino, actual, visitado)) {
                        return true;
                    }
                } else if (vecino != raiz) {
                    // Si el vecino ya está visitado y no es la raiz, se ha detectado un ciclo
                    return true;
                }
            }

            return false; // No se ha encontrado ningun ciclo en esta rama
        }

        /*
     * Determinau si els dos grafs són isomorfs. Podeu suposar que cap dels dos té ordre major que
     * 10.
         */
        static boolean exercici2(int[][] g1, int[][] g2) {
            int n = g1.length;
            if (g2.length != n) {
                return false; // Si los grafos no tienen el mismo numro de vertices, no son isomorfos
            }
            int[] permutacion = new int[n];
            for (int i = 0; i < n; i++) {
                permutacion[i] = i; // Inicializamos la permutación con el orden natural
            }
            do {
                // Comprobamos si con la permutacion actual, los grafos son isomorfos
                if (esIsomorfo(g1, g2, permutacion)) {
                    return true;
                }
            } while (sigPermut(permutacion)); // generamos la siguiente permutación

            return false; // Si ninguna permutacion funciona, no son isomorfos
        }

        static boolean esIsomorfo(int[][] g1, int[][] g2, int[] perm) {
            int n = g1.length;

            for (int i = 0; i < n; i++) {
                int u1 = i;
                int u2 = perm[i];

                int[] adj1 = g1[u1];
                int[] adj2 = g2[u2];

                if (adj1.length != adj2.length) {
                    return false; // si no tienen el mismo numero de adyacentes, no son isomorfos
                }
                int[] vecinosAdj1 = new int[adj1.length];
                for (int j = 0; j < adj1.length; j++) {
                    vecinosAdj1[j] = perm[adj1[j]]; // asignamos los vecinos segun la permutacion
                }

                Arrays.sort(vecinosAdj1); // ordenamos las listas para poder compararlas
                Arrays.sort(adj2);

                for (int j = 0; j < vecinosAdj1.length; j++) {
                    if (vecinosAdj1[j] != adj2[j]) {
                        return false; // si algun vecino no coincide, no son isomorfos
                    }
                }
            }

            return true; // todos los vecinos coinciden con la permutacion, son isomorfos
        }

        static boolean sigPermut(int[] a) {
            int i = a.length - 2;
            while (i >= 0 && a[i] >= a[i + 1]) {
                i--;
            }
            if (i < 0) {
                return false; // no hay mas permutaciones posibles
            }
            int j = a.length - 1;
            while (a[j] <= a[i]) {
                j--;
            }

            int tmp = a[i];
            a[i] = a[j];
            a[j] = tmp; // intercambiamos elementos para generar la siguiente permutación

            // invertimos la parte derecha para obtener la permutación lexicograficamente siguiente 
            for (int l = i + 1, r = a.length - 1; l < r; l++, r--) {
                tmp = a[l];
                a[l] = a[r];
                a[r] = tmp;
            }

            return true; // se genero la nueva permutacion 
        }


        /*
     * Determinau si el graf `g` (no dirigit) és un arbre. Si ho és, retornau el seu recorregut en
     * postordre desde el vèrtex `r`. Sinó, retornau null;
     *
     * En cas de ser un arbre, assumiu que l'ordre dels fills vé donat per l'array de veïns de cada
     * vèrtex.
         */
        static int[] exercici3(int[][] g, int r) {
            int n = g.length;
            boolean[] visited = new boolean[n];
            List<Integer> postordre = new ArrayList<>();

            // DFS auxiliar que devuelve false si detecta ciclo
            boolean esArbol = dfs(g, r, -1, visited, postordre);
            if (!esArbol) {
                return null;
            }

            // Comprobamos que todos los vertices son visitados
            for (boolean v : visited) {
                if (!v) {
                    return null; // no connexo → no es arbol
                }
            }

            // Convertimos la lista a array
            int[] resultat = new int[postordre.size()];
            for (int i = 0; i < postordre.size(); i++) {
                resultat[i] = postordre.get(i);
            }
            return resultat;
        }

        static boolean dfs(int[][] g, int actual, int padre, boolean[] visitado, List<Integer> postorden) {
            visitado[actual] = true;
            for (int vecino : g[actual]) {
                if (!visitado[vecino]) {
                    if (!dfs(g, vecino, actual, visitado, postorden)) {
                        return false; // ciclo detectado a nivel inferior
                    }
                } else if (vecino != padre) {
                    // vecino visitado que no es padre significa que es un ciclo
                    return false;
                }
            }
            postorden.add(actual); // añadimos en postordenr despues de visitar los hijos
            return true;
        }

        /*
     * Suposau que l'entrada és un mapa com el següent, donat com String per files (vegeu els tests)
     *
     *   _____________________________________
     *  |          #       #########      ####|
     *  |       O  # ###   #########  ##  ####|
     *  |    ####### ###   #########  ##      |
     *  |    ####  # ###   #########  ######  |
     *  |    ####    ###              ######  |
     *  |    ######################## ##      |
     *  |    ####                     ## D    |
     *  |_____________________________##______|
     *
     * Els límits del mapa els podeu considerar com els límits de l'array/String, no fa falta que
     * cerqueu els caràcters "_" i "|", i a més podeu suposar que el mapa és rectangular.
     *
     * Donau el nombre mínim de caselles que s'han de recorrer per anar de l'origen "O" fins al
     * destí "D" amb les següents regles:
     *  - No es pot sortir dels límits del mapa
     *  - No es pot passar per caselles "#"
     *  - No es pot anar en diagonal
     *
     * Si és impossible, retornau -1.
         */
        static int exercici4(char[][] mapa) {
            int[] dirX = {-1, 1, 0, 0}; // direcciones verticales arriba y abajo
            int[] dirY = {0, 0, -1, 1}; // direcciones orrizontales izq y der
            int n = mapa.length;
            int m = mapa[0].length;

            // buscamos las posiciones de la O (origen) y la D (destino)
            int xInicial = -1, yInicial = -1, xFinal = -1, yFinal = -1;
            for (int i = 0; i < n; i++) {
                for (int j = 0; j < m; j++) {
                    if (mapa[i][j] == 'O') {
                        xInicial = i;
                        yInicial = j;
                    }
                    if (mapa[i][j] == 'D') {
                        xFinal = i;
                        yFinal = j;
                    }
                }
            }

            // verificamos si falta alguna coordenada esencial
            if (xInicial == -1 || xFinal == -1) {
                return -1; // no se encontro origen o destinno
            }

            // preparamos la estructura para hacer el recorrido BFS
            ArrayList<int[]> cola = new ArrayList<>();
            boolean[][] visitado = new boolean[n][m]; // matriz para marcar lugares ya pasados

            // insertamos el punto inicial en la cola
            cola.add(new int[]{xInicial, yInicial, 0}); // almacenamos posicion y contador de pasos
            visitado[xInicial][yInicial] = true;

            // iniciamos el recorrido en anchura
            while (!cola.isEmpty()) {
                int[] actual = cola.remove(0); // sacamos el primero en entrar
                int x = actual[0];
                int y = actual[1];
                int saltos = actual[2];

                // Ss llegamos al punto de destino
                if (x == xFinal && y == yFinal) {
                    return saltos;
                }

                // movemos a las casillas vecinas (4 direcciones)
                for (int i = 0; i < 4; i++) {
                    int nuevaX = x + dirX[i];
                    int nuevaY = y + dirY[i];

                    // validamos que la nueva casilla sea segura y no visitda
                    if (nuevaX >= 0 && nuevaX < n && nuevaY >= 0 && nuevaY < m
                            && !visitado[nuevaX][nuevaY] && mapa[nuevaX][nuevaY] != '#') {
                        visitado[nuevaX][nuevaY] = true;
                        cola.add(new int[]{nuevaX, nuevaY, saltos + 1}); // añadimos nueva casilla con pasos aumentados
                    }
                }
            }

            // si no encontramos camino posible
            return -1;
        }


        /*
     * Aquí teniu alguns exemples i proves relacionades amb aquests exercicis (vegeu `main`)
         */
        static void tests() {

            final int[][] D2 = {{}, {}};
            final int[][] C3 = {{1, 2}, {0, 2}, {0, 1}};

            final int[][] T1 = {{1, 2}, {0}, {0}};
            final int[][] T2 = {{1}, {0, 2}, {1}};

            // Exercici 1
            // G té cicles?
            test(3, 1, 1, () -> !exercici1(D2));
            test(3, 1, 2, () -> exercici1(C3));

            // Exercici 2
            // Isomorfisme de grafs
            test(3, 2, 1, () -> exercici2(T1, T2));
            test(3, 2, 2, () -> !exercici2(T1, C3));

            // Exercici 3
            // Postordre
            test(3, 3, 1, () -> exercici3(C3, 1) == null);
            test(3, 3, 2, () -> Arrays.equals(exercici3(T1, 0), new int[]{1, 2, 0}));

            // Exercici 4
            // Laberint
            test(3, 4, 1, () -> {
                return -1 == exercici4(new char[][]{
                    " #O".toCharArray(),
                    "D# ".toCharArray(),
                    " # ".toCharArray(),});
            });

            test(3, 4, 2, () -> {
                return 8 == exercici4(new char[][]{
                    "###D".toCharArray(),
                    "O # ".toCharArray(),
                    " ## ".toCharArray(),
                    "    ".toCharArray(),});
            });
        }
    }

    /*
   * Aquí teniu els exercicis del Tema 4 (Aritmètica).
   *
   * En aquest tema no podeu:
   *  - Utilitzar la força bruta per resoldre equacions: és a dir, provar tots els nombres de 0 a n
   *    fins trobar el que funcioni.
   *  - Utilitzar long, float ni double.
   *
   * Si implementau algun dels exercicis així, tendreu un 0 d'aquell exercici.
     */
    static class Tema4 {

        /*
     * Primer, codificau el missatge en blocs de longitud 2 amb codificació ASCII. Després encriptau
     * el missatge utilitzant xifrat RSA amb la clau pública donada.
     *
     * Per obtenir els codis ASCII del String podeu utilitzar `msg.getBytes()`.
     *
     * Podeu suposar que:
     * - La longitud de `msg` és múltiple de 2
     * - El valor de tots els caràcters de `msg` està entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
     *
     * Pista: https://en.wikipedia.org/wiki/Exponentiation_by_squaring
         */
        static int[] exercici1(String msg, int n, int e) {
            // converitr el mensaje a bytes
            byte[] mensajeEnBytes = msg.getBytes();
            // calculamos cuantos bloques de 2 bytes hay en el mensaje
            // al dividir la longitud total del array de bytes entre 2
            // obtenemos el numero de pares de caracteres que formaran cada bloque
            int numBloques = mensajeEnBytes.length / 2;
            int[] encriptado = new int[numBloques];

            // hacemos 2 boques de caracteres  bloc = byte0*128 + byte1
            for (int i = 0; i < numBloques; i++) {
                // extraemos el primer byte del bloque y lo convertimos a entero sin signo multiplicando por -1 en hexa
                int bloque1 = mensajeEnBytes[2 * i] & 0xFF;
                // extraemos el segundo byte del bloque y lo convertimos a entero sin signo por -1 en hexa
                int bloque2 = mensajeEnBytes[2 * i + 1] & 0xFF;
                // unimos los dos valores en un solo entero haciendo primer byte * 128 + segundo byte
                int bloqueJunto = bloque1 * 128 + bloque2;

                // ahora encriptamos el bloque usando exponenciacionb modular
                long resultado = 1;
                long base = bloqueJunto % n;
                int exponente = e;
                // hacmemos el bucle hasta que llegue a 0
                while (exponente > 0) {
                    // si el bit menos significativo de exp es 1
                    // multiplicamos resultado por base y aplicamos % n
                    if ((exponente & 1) == 1) {
                        resultado = (resultado * base) % n;
                    }
                    // elevamos la base al cuadrado y hacemos el modulo para avanzar al siguiente bit
                    base = (base * base) % n;
                    // desplazamos exponente un bit a la derecha, basicamente dividir entre 2
                    exponente >>= 1;
                }
                encriptado[i] = (int) resultado;
            }
            return encriptado;
        }


        /*
     * Primer, desencriptau el missatge utilitzant xifrat RSA amb la clau pública donada. Després
     * descodificau el missatge en blocs de longitud 2 amb codificació ASCII (igual que l'exercici
     * anterior, però al revés).
     *
     * Per construir un String a partir d'un array de bytes podeu fer servir el constructor
     * `new String(byte[])`. Si heu de factoritzar algun nombre, ho podeu fer per força bruta.
     *
     * També podeu suposar que:
     * - La longitud del missatge original és múltiple de 2
     * - El valor de tots els caràcters originals estava entre 32 i 127.
     * - La clau pública (n, e) és de la forma vista a les transparències.
     * - n és major que 2¹⁴, i n² és menor que Integer.MAX_VALUE
         */
        static String exercici2(int[] bloquesCifrados, int moduloo, int exponente) {
            //  factorizamos de n en p i q por fuerza bruta(lo pone el enunciado)
            int p = 0, q = 0;
            for (int i = 2; i * i <= moduloo; i++) {
                if (moduloo % i == 0) {
                    p = i;
                    q = moduloo / i;
                    break;
                }
            }
            // si da 0, invocamos la excepcion
            if (p == 0) {
                throw new IllegalArgumentException("no se pudo factorizar n, que es" + moduloo);
            }

            // calculamos fi (p - 1) * (q - 1)
            int fi = (p - 1) * (q - 1);

            // calculo la clave privada d que es el inverso exponente % fi
            int a = exponente, b = fi;
            int x = 1, xx = 0;
            while (b != 0) {
                int cociente = a / b;
                int resto = a % b;
                a = b;
                b = resto;
                resto = x - cociente * xx;
                x = xx;
                xx = resto;
            }
            if (a != 1) {
                throw new ArithmeticException("no existe el inverso " + exponente + " % " + fi);
            }
            int d = x;
            if (d < 0) {
                d += fi;
                // miramos que d sea positivo si o si
            }

            // descrifrar y construir los bytes
            byte[] resultadoEnBytes = new byte[bloquesCifrados.length * 2];
            int indice = 0;
            for (int bloque : bloquesCifrados) {
                // calcula bloque^d % modulo de forma rápida
                // va procesando bit a bit el exponente d, multiplicando al resultado
                // sólo cuando el bit es 1 y haciendo al cuadrado la base en cada paso
                long valor = 1;
                long base = bloque % moduloo;
                int exp = d;
                // recorremos bit a bit exp hasta que sea cero
                while (exp > 0) {
                    // si el bit menos significativo d exp es 1, multiplicamos
                    // valor por la base y hacemos el módulo
                    if ((exp & 1) == 1) {
                        // elevamos la base al cuadrado y hacemos el % con modulo para el siguiente bit
                        valor = (valor * base) % moduloo;
                    }
                    base = (base * base) % moduloo;
                    // desplazars exp un bit a la derecha , como si dividieramos por 2
                    exp >>= 1;
                }
                int block = (int) valor;
                // convertir el enetero en dos caracteres ascii con base 128
                resultadoEnBytes[indice++] = (byte) (block / 128);
                resultadoEnBytes[indice++] = (byte) (block % 128);
            }

            /// devolvemos el string
            return new String(resultadoEnBytes);
        }

        static void tests() {
            // Exercici 1
            // Codificar i encriptar
            test(4, 1, 1, () -> {
                var n = 2 * 8209;
                var e = 5;

                var encr = exercici1("Patata", n, e);
                return Arrays.equals(encr, new int[]{4907, 4785, 4785});
            });

            // Exercici 2
            // Desencriptar i decodificar
            test(4, 2, 1, () -> {
                var n = 2 * 8209;
                var e = 5;

                var encr = new int[]{4907, 4785, 4785};
                var decr = exercici2(encr, n, e);
                return "Patata".equals(decr);
            });
        }
    }

    /*
   * Aquest mètode `main` conté alguns exemples de paràmetres i dels resultats que haurien de donar
   * els exercicis. Podeu utilitzar-los de guia i també en podeu afegir d'altres (no els tendrem en
   * compte, però és molt recomanable).
   *
   * Podeu aprofitar el mètode `test` per comprovar fàcilment que un valor sigui `true`.
     */
    public static void main(String[] args) {
        System.out.println("---- Tema 1 ----");
        Tema1.tests();
        System.out.println("---- Tema 2 ----");
        Tema2.tests();
        System.out.println("---- Tema 3 ----");
        Tema3.tests();
        System.out.println("---- Tema 4 ----");
        Tema4.tests();
    }

    // Informa sobre el resultat de p, juntament amb quin tema, exercici i test es correspon.
    static void test(int tema, int exercici, int test, BooleanSupplier p) {
        try {
            if (p.getAsBoolean()) {
                System.out.printf("Tema %d, exercici %d, test %d: OK\n", tema, exercici, test);
            } else {
                System.out.printf("Tema %d, exercici %d, test %d: Error\n", tema, exercici, test);
            }
        } catch (Exception e) {
            if (e instanceof UnsupportedOperationException && "pendent".equals(e.getMessage())) {
                System.out.printf("Tema %d, exercici %d, test %d: Pendent\n", tema, exercici, test);
            } else {
                System.out.printf("Tema %d, exercici %d, test %d: Excepció\n", tema, exercici, test);
                e.printStackTrace();
            }
        }
    }
}

// vim: set textwidth=100 shiftwidth=2 expandtab :

import com.github.ajalt.clikt.core.CliktCommand
import com.github.ajalt.clikt.parameters.types.file
import com.github.ajalt.clikt.parameters.types.int
import com.github.ajalt.clikt.core.BadParameterValue
import com.github.ajalt.clikt.core.subcommands
import com.github.ajalt.clikt.parameters.options.*
import com.github.ajalt.clikt.parameters.types.enum
import java.io.File
import java.lang.Integer.max
import java.math.BigDecimal
import java.math.RoundingMode
import java.util.*
import kotlin.math.log2

val grover = """def groverDiffusion[n:!ℕ](cand:uint[n])mfree:uint[n] {
    for k in [0..n) { cand[k] := H(cand[k]); }
    if cand!=0{ phase(π); }
    for k in [0..n) { cand[k] := H(cand[k]); }
    return cand;
}

def grover_j[n:!ℕ,j:!ℕ](f: const uint[n] !→ lifted 𝔹):!ℕ{
	// nIterations:=ceil((π/4)·sqrt((2^n)/nrOfSolutions));
	cand:=0:uint[n];
    for k in [0..n){ cand[k]:=H(cand[k]); }
	for k in [0..j){
		if f(cand){ phase(π); }
		cand:=groverDiffusion(cand);
	}
	return measure(cand) as !ℕ;
}

// Popular Lehmer generator that uses the prime modulus 2^32−5
def random(state:!ℕ):(!ℕ)×(!ℚ) {
	upperlimit := (2^32 - 5);
	newstate := (state · 279470273) % upperlimit;
    newstateQ := newstate as !ℚ; // for the following division to get a rational number
	return (newstate, newstateQ / upperlimit);
}

def grover_unknown_k_one_iteration[n:!ℕ](f: const uint[n] !→ lifted 𝔹,t: !ℕ !→ !𝔹, seed:!ℕ):(!ℤ)×(!ℕ) {
	l := 6/5;
	m := 1 as !ℝ;
	state := seed;
	flag := true;
	while(flag){
		(zstate, z) := random(state);
		state = zstate;
		j := floor(z·m) coerce !ℕ;
		print(state);
		result := grover_j[n,j](f);
		if(t(result)){
			return (result, state) as (!ℤ)×(!ℕ);
		}
		if(m>=sqrt(2^n)){ // it might be that there are many solutions and m=sqrt(n) has unluckily already been reached => better to restart with m=1 in this case to faster find a solution!
			flag = false;
		}
		m = min(l·m, sqrt(n));
	}
	return (-1, state) as (!ℤ)×(!ℕ);
}

def grover_unknown_k_repeating[n:!ℕ](f: const uint[n] !→ lifted 𝔹,t: !ℕ !→ !𝔹, seed:!ℕ):!ℕ {
	state := seed;
	while(true){
		(result, zstate) := grover_unknown_k_one_iteration[n](f, t, state);
		state = zstate;
		if(result>=0){
			return result coerce !ℕ;
		}
	}
}

def grover_unknown_k[n:!ℕ](f: const uint[n] !→ lifted 𝔹,t: !ℕ !→ !𝔹):!ℕ {
	return grover_unknown_k_repeating[n](f, t, 1);
}

"""

// TODO: include in code generator
val deterministic_grover = """
// Deterministic approach of Grover's search algorithm
// https://link.springer.com/chapter/10.1007/3-540-44679-6_55
def deterministic_grover[n:!ℕ](f: const uint[n] !→ lifted 𝔹,t: !ℕ !→ !𝔹):!ℕ {
    k := 4;
    i := 1;
    while true{
        j := 2^i;
        for m in [0..k){
            result := grover_j[n,j](f);
            if t(result){
                return result;
            }
        }
    }
}

"""

val facul = """def facul(i:!ℤ)lifted:!ℤ{
	if i==1{
		return i;
	} else {
		return i*facul(i-1);
	}
}
    
"""

val numberToPermutation = """// calculates a permutation from a given number in O(pl), where pl is the length of the permutation
// z is the number of bits used to represent one number in the permutation list
// n is the number of bits used to represent the permutation number
def numberToPermutation[n:!ℕ,pl:!ℕ,z:!ℕ](const k:uint[n]) qfree {
    ml:=vector(pl,0:uint[z]); // help vector to generate permutation
    r:=vector(pl,0:uint[z]); // stores permutation -> result!
    for i in[0..pl){
        ml[i] = i as uint[z]; // initialize help vector (0, 1, 2, ..., pl-1)
    }
    l:=dup(k); // duplicate quantum variable, as otherwise it is already consumed...
    for i in[0..pl){
        ind := l%(pl-i); // choose current number in permutation from 0 to pl-i in help vector
        l = l div (pl-i); // for determining the remaining permutation list
        r[i] = ml[ind]; // current number in permutation list...
        ml[ind] = ml[pl-i-1]; // ml[ind] is now in the permutation -> swap with last number in help vector, such that it is not taken any more for the remaining permutation list
    }
    return r;
}

"""

val checkScheduleStart = """def checkSchedule[n:!ℕ,u:!ℕ](config:uint[n])lifted:𝔹 {
    res := true:𝔹;
    limits := array(m,0) as uint[n][];
    last := 0:uint[n];
    r := config;
    for i in [0..m-1){ // determine limits of which transactions (in the permutation list) are to be executed on which machine...
        limits[i] = r % T.length;
        r = r div T.length;
        if limits[i]<=last { // check if limits are strictly increasing
            res = false;
        }
        last = limits[i];
    }
    limits[m-1] = T.length-1 as !uint[n];
    z:=ceil(log(facul(T.length))/log(2)) coerce !ℕ;
    permutation := numberToPermutation[n,T.length,z](r);
"""

val checkResult = """def checkResult[n:!ℕ,u:!ℕ](r:!ℕ):!𝔹{
	check := true;
	rv := r;
	limit := array(m,0);
	for i in [0..m-1){
		limit[i] = rv % T.length;
		rv = rv div T.length;
	}
	limit[m-1] = T.length-1 coerce !ℕ;
	z:=ceil(log(facul(T.length))/log(2)) coerce !ℕ;
	permutation := numberToPermutation[n,T.length,z](rv as !uint[n]);
	s := 0;
    firstStartOfConflict := array(C.length,0);
    firstEndOfConflict := array(C.length,0);
    secondStartOfConflict := array(C.length,0);
    secondEndOfConflict := array(C.length,0);
	for i in [0..m){
		runtime := 0;
		for j in [s..limit[i]+1){ // [s..limit[i]+1) = [s..limit[i]], but latter is currently not supported by silq compiler! 
            for c in [0..C.length) {
                if permutation[j]==C[c][0] {
                    firstStartOfConflict[c] = runtime;
                }
                if permutation[j]==C[c][1] {
                    secondStartOfConflict[c] = runtime;
                }
            }
			runtime += T[permutation[j]];
            for c in [0..C.length) {
                if permutation[j]==C[c][0] {
                    firstEndOfConflict[c] = runtime;
                }
                if permutation[j]==C[c][1] {
                    secondEndOfConflict[c] = runtime;
                }
            }
		}
		s = limit[i]+1;
		if(runtime>u){
			check = false;
		}
	}
    for c in [0..C.length) {
        if !(firstEndOfConflict[c] <= secondStartOfConflict[c] || secondEndOfConflict[c] <= firstStartOfConflict[c]){
            check = false;
        }
    }
	return check;
}

def printResult[n:!ℕ](r:!ℕ) {
	check := true;
	rv := r;
	limit := array(m,0);
	for i in [0..m-1){
		limit[i] = rv % T.length;
		print(limit[i]);
		rv = rv div T.length;
	}
	limit[m-1] = T.length-1 coerce !ℕ;
    print(limit[m-1]);
	z:=ceil(log(facul(T.length))/log(2)) coerce !ℕ;
	permutation := numberToPermutation[n,T.length,z](rv as !uint[n]);
	print(permutation);
	s := 0;
	for i in [0..m){
		runtime := 0;
		for j in [s..limit[i]+1){ // [s..limit[i]+1) = [s..limit[i]], but latter is currently not supported by silq compiler! 
			runtime += T[permutation[j]];
		}
		s = limit[i]+1;
		print(i);
		print(runtime);
	}
}
    
"""

val optimizeSchedule = """def optimizeSchedule[bits:!ℕ]():!ℕ {
    // initialize the seed of the random number generator
	state := 1;
    // initialize upper limit of runtime
    R := maxLength;
    delta := 1;
	while(true){
        print(R);
        // apply grover's search algorithm to optimizing transaction schedule problem
		(result, zstate) := grover_unknown_k_one_iteration[bits](checkSchedule[bits, R], checkResult[bits, R], state);
		state = zstate;
		if(result>=0){
			return result coerce !ℕ;
		}
        // increase upper limit of runtime
        R = R + delta;
        // double the increment for increasing the upper limit
        delta = delta*2;
	}
}

"""

val mainFct = """def main(){
	// calculate number of needed bits:
	bits := ceil(log(T.length+1)/log(2))*(m-1)+ceil(log(facul(T.length))/log(2)) coerce !ℕ;
    res:= optimizeSchedule[bits]();
	printResult[bits](res);
	return res as !ℤ;
}

"""

class MutablePair<f, s>(var first:s, var second:s){
 override fun toString() = "[${this.first}, ${this.second}]"
}

class CodeGenerator(val machines:Int, val transactionsLengths:List<Int>, val conflicts:List<MutablePair<Int, Int>>){
    var numberOfConflictingTransactions = 0
    val transactions = Array<Int>(this.transactionsLengths.size){ 0 }
    fun generate():String {
        // first reorder transactions, such that transactions with conflicts are first in the list (up to index numberOfConflictingTransactions)
        val conflictingTransactions = mutableSetOf<Int>()
        for(t in this.conflicts){
            conflictingTransactions += t.first
            conflictingTransactions += t.second
        }
        this.numberOfConflictingTransactions = conflictingTransactions.size
        val remainingTransactions = mutableSetOf<Int>()
        remainingTransactions.addAll(0 until this.transactionsLengths.size)
        remainingTransactions.removeAll(conflictingTransactions)
        val map = Array<Int>(this.transactionsLengths.size){
            val search = conflictingTransactions.indexOf(it)
            if(search<0){
                remainingTransactions.indexOf(it)
            } else {
                search
            }
        };
        val mapInverse = Array<Int>(this.transactionsLengths.size){ 0 }
        (0 until map.size).forEach{
            mapInverse[map[it]] = it
        }
        (0 until this.transactionsLengths.size).forEach{
            this.transactions[it] = this.transactionsLengths[mapInverse[it]]
        }
        // mapping the transaction ids in conflicts to new transaction ids...
        this.conflicts.forEach{
            it.first = map[it.first]
            it.second = map[it.second]
        }
        val t = "T := ${Arrays.toString(this.transactions)}; // lengths of transactions" + System.lineSeparator()
        val m = "m := ${this.machines}; // number of machines" + System.lineSeparator()
        val c = "C := [${this.conflicts.map{"[" + it.first.toString() + "," + it.second.toString() + "]"}.joinToString(",")}]; // conflicts of transactions" + System.lineSeparator()
        val maxLength = max(transactions.maxOrNull()?:0,((this.transactions.sum()-1)/this.machines)+1) // -1...+1 in order to simulate ceil with integer division...
        val mL = "maxLength := $maxLength; // maximum runtime" + System.lineSeparator()
        return  grover +
                numberToPermutation +
                facul +
                t +
                m +
                c +
                mL +
                System.lineSeparator() +
                generateCheckSchedule() +
                checkResult +
                optimizeSchedule +
                mainFct
    }

    fun generateCheckSchedule():String {
        val bitsForCheckOfMaxLength = Math.ceil(Math.log((this.transactions.sum()+1).toDouble())).toInt()
        return  checkScheduleStart +
                this.transactions.indices.map{generateGetLength(bitsForCheckOfMaxLength,it)}.joinToString(System.lineSeparator()) +
                System.lineSeparator() +
                (0..this.numberOfConflictingTransactions-1).map{
                    "    f${it}s := 0 as uint[$bitsForCheckOfMaxLength];" +
                    System.lineSeparator() +
                    "    f${it}e := 0 as uint[$bitsForCheckOfMaxLength];" +
                    System.lineSeparator()
                }.joinToString("") +
                "    " +
                checkMaxLengthOnEachMachine(bitsForCheckOfMaxLength) +
                if(this.conflicts.isEmpty()) ""
                else {
                    this.conflicts.map {
                    "    if !(f${it.first}e <= f${it.second}s || f${it.second}e <= f${it.first}s) {" +
                    System.lineSeparator() +
                    "        res = false;" +
                    System.lineSeparator() +
                    "    }" +
                    System.lineSeparator()
                    }.joinToString("")
                } +
                "    return res;" +
                System.lineSeparator() +
                "}" +
                System.lineSeparator()
    }

    fun generateGetLength(bits:Int, ti:Int): String =
        "    t$ti := 0:uint[$bits];" +
        System.lineSeparator() +
        "    " +
        this.transactions.indices.map{
            "if permutation[$ti]==$it {" +
            System.lineSeparator() +
            "        t$ti = ${this.transactions[it]} as uint[$bits];" +
            System.lineSeparator() +
            "    }"
        }.joinToString(" else ")

    fun checkMaxLengthOnEachMachine(bitsForCheckOfMaxLength:Int, i:Int=0, start:Int=0, indent:String="    "):String =
        (start..this.transactions.size-1).map {
            "if limits[$i]==$it {" +
            System.lineSeparator() +
            checkMaxLengthForOneCase(bitsForCheckOfMaxLength, i, start, it, "$indent    ") +
            (if(i+1<this.machines) indent + "    " + checkMaxLengthOnEachMachine(bitsForCheckOfMaxLength, i+1,it+1, "$indent    ")
            else checkMaxLengthForOneCase(bitsForCheckOfMaxLength, i+1, it+1, this.transactions.size-1, "$indent    ")) +
            indent + "}"
        }.joinToString(" else ") +
        System.lineSeparator()

    fun checkMaxLengthForOneCase(bitsForCheckOfMaxLength:Int, i:Int=0, start:Int=0, end:Int, indent:String="    "):String =
        if(start<=end) {
            indent + "sum0 := 0 as uint[3];" +
            System.lineSeparator() +
            (start..end).map {
                indent + "sum${it-start+1} := dup(sum${it-start}) + dup(t$it);"
            }.joinToString(System.lineSeparator()) +
            System.lineSeparator() +
            indent + "time$i := [sum0, " +
            (start..end).map {
                "sum${it-start+1}"
            }.joinToString(", ") +
            "];" +
            System.lineSeparator() +
            indent + "m${i}runtime := " +
            (start..end).map { "t${it}" }.joinToString(" + ") +
            ";" +
            System.lineSeparator() +
            indent + "if m${i}runtime>u {" +
            System.lineSeparator() +
            indent + "    res = false;" +
            System.lineSeparator() +
            indent + "}" +
            System.lineSeparator() +
            (start..end).map{ index ->
                indent + "if permutation[$index]<${this.numberOfConflictingTransactions} {" +
                System.lineSeparator() +
                generateDecisionTree(0, this.numberOfConflictingTransactions-1, i, start, index, indent + "    ") +
                indent + "}" +
                System.lineSeparator()
            }.joinToString("")
        } else ""

    fun generateDecisionTree(left:Int, right:Int, i:Int, start:Int, index:Int, indent:String="    "):String =
        if(left>=right)
            setRuntimeOfConflictingTransaction(i, start, index, left, indent)
        else indent+"if permutation[$index]<=${(left+right)/2} {" +
                System.lineSeparator() +
                generateDecisionTree(left, (left+right)/2, i, start, index, indent + "    ") +
                indent+"} else {" +
                System.lineSeparator() +
                generateDecisionTree((left+right)/2+1, right, i, start, index, indent + "    ") +
                indent+"}" +
                System.lineSeparator()

    fun setRuntimeOfConflictingTransaction(i:Int, start:Int, index:Int, tid:Int, indent:String="    ") =
        indent + "f${tid}s = time$i[${index-start}];" +
        System.lineSeparator() +
        indent + "f${tid}e = time$i[${index-start+1}];" +
        System.lineSeparator()
}

class CommandLineInterpretation : CliktCommand() {
    override fun run() = Unit
}

// call with e.g.: code -m 2 -t 3,6,2,4 -c 1-2,2-3 -o C:\Luebeck\SILQ\Generated.slq
// call with e.g.: code -m 2 -t 3,6,3 -c 1-2,2-3 -o C:\Luebeck\SILQ\Generated.slq
class Code : CliktCommand(help="Generating the code for the Silq quantum simulator") {
    // define command line parameters
    val machines: Int by option("-m", "--machines", "--numberofmachines", "--cores", "--numberofcores", help = "Number of machines / cores / compute units").int().default(4)
    val transactions by option("-t", "--transactions", "--lengthsoftransactions", help = "Lengths of transactions (separated by comma (','))").convert{it.split(",").map{it.toInt()}}.default(listOf(3, 6, 2, 5))
    val conflicts by option("-c", "--conflicts", help = "Conflicting transactions in the form 'T1-T2,T2-T4', where Ti is the transaction id, e.g. '1-2,5-6' for conflicts between the transactions 1 and 2, and 5 and 6!").convert{it.split(",").map{
        val c = it.split("-").map{it.toInt()}
        if(c.size!=2){
            throw BadParameterValue("Conflicting transactions should be of the form 'T1-T2,T3-T4,...', where Ti is the transaction id, e.g. '1-2,5-6'")
        }
        MutablePair<Int, Int>(c[0], c[1])
    }}.default(listOf())
    val outputfile by option("-o", "--output", "-f", "--file", help = "Output file to which the generated code is written...").file(mustExist=false, canBeDir=false)

    override fun run() {
        if(this.outputfile != null) {
            echo("Machines: ${this.machines}")
            echo("Transactions with lengths: ${this.transactions}")
            echo("Conflicts: ${this.conflicts}")
            echo("Output file: ${this.outputfile}")
        }
        val codeGenerator = CodeGenerator(this.machines, this.transactions, this.conflicts)
        val code = codeGenerator.generate()
        if(this.outputfile != null){
            this.outputfile!!.writeText(code)
        } else {
            println(code)
        }
    }
}

// call with e.g.: solutions -m 2 -t 5,3,2 -c 1-2 -o C:\Luebeck\SILQ\Generated.slq
class Solutions : CliktCommand(help="Calculating the number of solutions for the optimizing transaction schedule problem") {
    // define command line parameters
    val machines: Int by option("-m", "--machines", "--numberofmachines", "--cores", "--numberofcores", help = "Number of machines / cores / compute units").int().default(4)
    val transactions by option("-t", "--transactions", "--lengthsoftransactions", help = "Lengths of transactions (separated by comma (','))").convert{it.split(",").map{it.toInt()}}.default(listOf(3, 6, 2, 5))
    val conflicts by option("-c", "--conflicts", help = "Conflicting transactions in the form 'T1-T2,T2-T4', where Ti is the transaction id, e.g. '1-2,5-6' for conflicts between the transactions 1 and 2, and 5 and 6!").convert{it.split(",").map{
        val c = it.split("-").map{it.toInt()}
        if(c.size!=2){
            throw BadParameterValue("Conflicting transactions should be of the form 'T1-T2,T3-T4,...', where Ti is the transaction id, e.g. '1-2,5-6'")
        }
        MutablePair<Int, Int>(c[0], c[1])
    }}.default(listOf())
    val outputfile by option("-o", "--output", "-f", "--file", help = "Output file to which the result is written...").file(mustExist=false, canBeDir=false)

    override fun run() {
        val numberOfSolutions = NumberOfSolutions(this.machines, this.transactions, this.conflicts)
        val runtimes = numberOfSolutions.determineRuntimes()
        runtimes.printOut()
    }
}

// call with e.g.: normaldistribution -m 2 -t 10 -l 10 -s 1 -c 0
class Normaldistribution : CliktCommand(help="Calculating the number of solutions for the optimizing transaction schedule problem by using a normal distribution of the transaction lengths") {
    // define command line parameters
    val machines: Int by option("-m", "--machines", "--numberofmachines", "--cores", "--numberofcores", help = "Number of machines / cores / compute units").int().default(4)
    val transactions:Int by option("-t", "--transactions", help = "Number of transactions").int().default(10)
    val length:Int by option("-l", "--length", help = "The median of transaction lengths").int().default(10)
    val standarddeviation by option("-s", "--standard", "--standarddeviation", help = "The standard deviation of transaction lengths").int().default(1)
    val conflicts by option("-c", "--conflicts", help = "Percentage of conflicts").int().default(0)
    val outputfile by option("-o", "--output", "-f", "--file", help = "Output file to which the result is written...").file(mustExist=false, canBeDir=false)

    override fun run() {
        val transactionsLengths = transactionLengthsAccordingToNormalDistribution(this.transactions, this.length, this.standarddeviation)
        val conflictsList = randomConflictingTransactions(this.transactions, this.conflicts)
        val numberOfSolutions = NumberOfSolutions(this.machines, transactionsLengths, conflictsList)
        val runtimes = numberOfSolutions.determineRuntimes()
        runtimes.printOut()
    }
}

fun RawOption.intRange() = convert{it.split(":","-").map{it.toInt()}}

fun String.addLegendEntry() = "\\addlegendentry{$this}${System.lineSeparator()}"

fun String.createPlot(xLabel:String, yLabel:String, caption:String, label:String, columns:Int = 1, logy:Boolean = false) = """\begin{figure}[h]
  \centering
  \begin{tikzpicture}
     \begin{axis}[
        legend columns=${columns},
        legend style={at={(0.44,-0.17)},anchor=north,legend cell align=left},
        xlabel near ticks,
        ylabel near ticks,
        xlabel={ """ + xLabel + """ },
        ylabel={ """ + yLabel + """ },""" + (if(logy) " ymode=log," else "") + """
     ]
""" + this + """
     \end{axis}
  \end{tikzpicture}
  \caption{""" + caption + """}  
  \label{""" + label + """}
\end{figure}
"""

fun Double.round(scale:Int) = BigDecimal(this).setScale(scale, RoundingMode.HALF_EVEN)

fun String.addCommaIfNotBlank() = this + (if(this.isNotBlank()) ", " else "")

// call with e.g.: charts -m 2-4:2 -t 12 -l 10 -s 1-1:1 -c 0-20:10 -o C:\Gitlab\TransactionScheduleOptimizerViaQuantumComputing\paper\ronpubjournal\CumulativeNumberOfSolutionsVsRuntime.tex
// call with e.g.: charts -m 2 -t 10 -l 10 -s 1-3:1 -c 0-20:5 -o C:\Gitlab\TransactionScheduleOptimizerViaQuantumComputing\paper\ronpubjournal\CumulativeNumberOfSolutionsVsRuntime.tex
class Charts : CliktCommand(help="Computing the cumulative number of solutions distribution in relation to runtime") {
    // define command line parameters
    val machines by option(
        "-m",
        "--machines",
        "--numberofmachines",
        "--cores",
        "--numberofcores",
        help = "Number of machines / cores / compute units in the form m1-m2:n, i.e., ranging from m1 to m2 with step n. If step = 0, then the steps follow the powers of 2..."
    ).intRange().default(listOf(2,32,0))
    val transactions: Int by option("-t", "--transactions", help = "Number of transactions").int().default(10)
    val length: Int by option("-l", "--length", help = "The median of transaction lengths").int().default(10)
    val standarddeviation by option(
        "-s",
        "--standard",
        "--standarddeviation",
        help = "The standard deviation of transaction lengths in the form s1-s2:n, i.e., ranging from s1 to s2 with step n"
    ).intRange().default(listOf(1, 1, 1))
        .check("There must be three values given for the range in the form of s1-s2:n") { it.size == 3 }
    val conflicts by option(
        "-c",
        "--conflicts",
        help = "Conflicts in percentage to the number of transactions in the form c1-c2:n, i.e., ranging from c1 to c2 with step n"
    ).intRange().default(listOf(0, 0, 0))
        .check("There must be three values given for the range in the form of s1-s2:n") { it.size == 3 }
    val outputfile by option(
        "-o",
        "--output",
        "-f",
        "--file",
        help = "Output file to which the result is written..."
    ).file(mustExist = false, canBeDir = false)
    val experiments by option(
        "-e",
        "--experiments",
        help = "Prefix of the output file to which the results of the experiments are written..."
    ).file(mustExist = false, canBeDir = false)


    fun generateLegendEntry(minMachines:Int, maxMachines:Int, k:Int, minStandardDeviation:Int, maxStandardDeviation:Int, s:Int, minConflicts:Int, maxConflicts:Int, c:Int):String {
        var legendentry = ""
        if (minMachines != maxMachines) {
            legendentry += "\$m\$ = $k"
        }
        if (minStandardDeviation != maxStandardDeviation) {
            legendentry = legendentry.addCommaIfNotBlank() + "\$\\sigma_{|t_i|}\$ = $s"
        }
        if (minConflicts != maxConflicts) {
            legendentry = legendentry.addCommaIfNotBlank() + "\$|O| = n \\cdot ${c}\\%\$"
        }
        return legendentry
    }

    fun writeOutput(toWrite:String, postfixOfFilename:String) {
        if (this.outputfile == null) {
            println(toWrite)
        } else {
            val chartOutputFile = File(this.outputfile!!.absolutePath+postfixOfFilename+".tex")
            chartOutputFile.writeText(toWrite)
        }
    }

    fun generateParameters(minMachines:Int, maxMachines:Int, minStandardDeviation:Int, maxStandardDeviation:Int, minConflicts:Int, maxConflicts:Int):String {
        var parameters = "\$\\widetilde{|t_i|}\$ = ${this.transactions}"
        if (minStandardDeviation == maxStandardDeviation) {
            parameters += ", \$\\sigma_{|t_i|}\$ = $minStandardDeviation"
        }
        if (minConflicts == maxConflicts) {
            parameters += ", \$|C|\$ = $minConflicts\\%"
        }
        if (minMachines == maxMachines) {
            parameters += ", \$k\$ = $minMachines"
        }
        return parameters
    }

    override fun run() {
        val mapOfRuntimes = HashMap<Triple<Int, Int, Int>, Runtimes>()
        println("Number of machines: ${this.machines}")
        println("Number of transactions: ${this.transactions}")
        println("Median of transaction lengths: ${this.length}")
        val minConflicts = this.conflicts[0]
        val maxConflicts = this.conflicts[1]
        val stepConflicts = this.conflicts[2]
        val minStandardDeviation = this.standarddeviation[0]
        val maxStandardDeviation = this.standarddeviation[1]
        val stepStandardDeviation = this.standarddeviation[2]
        val minMachines = this.machines[0]
        val maxMachines = this.machines[1]
        val stepMachines = this.machines[2]
        var k = minMachines
        var i = log2(minMachines.toDouble()).toInt()
        while(k <= maxMachines) {
            for (c in minConflicts..maxConflicts step stepConflicts) {
                println("Conflicts in percentage to number of transactions: $c")
                for (s in minStandardDeviation..maxStandardDeviation step stepStandardDeviation) {
                    println("Standard deviation: $s")
                    val transactionsLengths =
                        transactionLengthsAccordingToNormalDistribution(this.transactions, this.length, s)
                    val conflictsList = randomConflictingTransactions(
                        this.transactions,
                        Math.round(this.transactions.toDouble() * c.toDouble() / 100.0).toInt()
                    )
                    println("k: $k")
                    println("n = ${this.transactions}, transactionsLengths: $transactionsLengths")
                    println("|C| = $c%, conflictsList: $conflictsList")
                    val numberOfSolutions = NumberOfSolutions(k, transactionsLengths, conflictsList)
                    val runtimes = numberOfSolutions.determineRuntimes(File(this.experiments!!.absolutePath + "${this.transactions}n${this.length}length${k}Machines${c}Conflicts${s}StandardDeviation"))
                    runtimes.printOut()
                    mapOfRuntimes[Triple(k,c,s)] = runtimes
                }
            }
            if(stepMachines==0) {
                i++
                k = Math.pow(2.0,i.toDouble()).toInt()
            } else {
                k += stepMachines
            }
        }
        // generate description of parameters to be used in the caption of various charts...
        var parameters = generateParameters(minMachines, maxMachines, minStandardDeviation, maxStandardDeviation, minConflicts, maxConflicts)
        // now generate charts for different standard deviations (otherwise too many lines): normalized cumulative number of solutions in relation to optimal runtime
        for (s in minStandardDeviation..maxStandardDeviation step stepStandardDeviation) {
            var plots = ""
            k = minMachines
            i = log2(minMachines.toDouble()).toInt()
            while (k <= maxMachines) {
                for (c in minConflicts..maxConflicts step stepConflicts) {
                    println("Conflicts in percentage to number of transactions: $c")
                    val legendentry = generateLegendEntry(
                        minMachines,
                        maxMachines,
                        k,
                        s,
                        s,
                        s,
                        minConflicts,
                        maxConflicts,
                        c
                    )
                    val runtimes = mapOfRuntimes[Triple(k, c, s)]
                    plots += runtimes!!.addCumulativePlotVsRopt()
                    plots += legendentry.addLegendEntry()
                }
                if (stepMachines == 0) {
                    i++
                    k = Math.pow(2.0, i.toDouble()).toInt()
                } else {
                    k += stepMachines
                }
            }
            var parametersFixedStandardDeviation = generateParameters(minMachines, maxMachines, s, s, minConflicts, maxConflicts)
            val resultNormalizedCumulativeNumberOfSolutionsVsRuntime = plots.createPlot(
                "\$R\$ as factor of \$R_{opt}\$",
                "\$S_{Normalized}(x)\$",
                "Normalized cumulative number of solutions \$S_{Normalized}(x) = \\frac{|S_{R\\leq x}|}{|S|}\$ in relation to runtime ($parametersFixedStandardDeviation).",
                "fig:NormalizedCumulativeNumberOfSolutionsVsRuntime",
                2
            )
            writeOutput(resultNormalizedCumulativeNumberOfSolutionsVsRuntime, "NormalizedCumulativeNumberOfSolutionsVsRuntime${s}StandardDeviation")
        }
        // now absolute numbers...
        for (s in minStandardDeviation..maxStandardDeviation step stepStandardDeviation) {
            var plots = ""
            k = minMachines
            i = log2(minMachines.toDouble()).toInt()
            while (k <= maxMachines) {
                for (c in minConflicts..maxConflicts step stepConflicts) {
                    println("Conflicts in percentage to number of transactions: $c")
                    val legendentry = generateLegendEntry(
                        minMachines,
                        maxMachines,
                        k,
                        s,
                        s,
                        s,
                        minConflicts,
                        maxConflicts,
                        c
                    )
                    val runtimes = mapOfRuntimes[Triple(k, c, s)]
                    plots += runtimes!!.addAbsoluteCumulativePlotVsRopt()
                    plots += legendentry.addLegendEntry()
                }
                if (stepMachines == 0) {
                    i++
                    k = Math.pow(2.0, i.toDouble()).toInt()
                } else {
                    k += stepMachines
                }
            }
            var parametersFixedStandardDeviation = generateParameters(minMachines, maxMachines, s, s, minConflicts, maxConflicts)
            val resultCumulativeNumberOfSolutionsVsRuntime = plots.createPlot(
                "\$R\$ as factor of \$R_{opt}\$",
                "\$|S_{R\\leq x}|\$",
                "Cumulative number of solutions \$|S_{R\\leq x}|\$ in relation to runtime ($parametersFixedStandardDeviation).",
                "fig:CumulativeNumberOfSolutionsVsRuntime",
                2,
                true
            )
            writeOutput(resultCumulativeNumberOfSolutionsVsRuntime, "CumulativeNumberOfSolutionsVsRuntime${s}StandardDeviation")
        }
        // generate chart NumberOfSolutionsVsK
        // different factors of R_opt
        for (s in minStandardDeviation..maxStandardDeviation step stepStandardDeviation) {
            for (c in minConflicts..maxConflicts step stepConflicts) {
                var plots = ""
                for (factorOfRopt in listOf(100,120,140,160,180,200)) {
                    plots += mapOfRuntimes.addCumulativePlotVsK(minMachines, maxMachines, stepMachines, c, s, factorOfRopt)
                    plots += "\$m\$ = ${factorOfRopt}\\% $\\cdot R_{opt}$".addLegendEntry()
                }
                var parametersFixedStandardDeviation =
                    generateParameters(minMachines, maxMachines, s, s, c, c)
                val resultNumberOfSolutionsVsk = plots.createPlot(
                    "\$k\$",
                    "\$S_{Normalized}(m)\$",
                    "Normalized cumulative number of solutions \$S_{Normalized}(m) = \\frac{|S_{R\\leq m'}|}{|S|}\$ with minimizing \$m'\\leq m\$, such that \$S_{R\\leq m'}\$ exists, in relation to \$k\$ ($parametersFixedStandardDeviation).",
                    "fig:NumberOfSolutionsVsk${s}StandardDeviation${c}Conflicts",
                    2
                )
                writeOutput(
                    resultNumberOfSolutionsVsk,
                    "NumberOfSolutionsVsk${s}StandardDeviation${c}Conflicts"
                )
            }
        }
        // R_opt and increasing number of conflicting transactions
        for (s in minStandardDeviation..maxStandardDeviation step stepStandardDeviation) {
            for (factorOfRopt in listOf(100,120,140,160,180,200)) {
                var plots = ""
                for (c in minConflicts..maxConflicts step stepConflicts) {
                    plots += mapOfRuntimes.addCumulativePlotVsK(
                        minMachines,
                        maxMachines,
                        stepMachines,
                        c,
                        s,
                        factorOfRopt
                    )
                    plots += "\$|C|\$ = $c\\%".addLegendEntry()
                }
                var parametersFixedStandardDeviation =
                    generateParameters(minMachines, maxMachines, s, s, minConflicts, maxConflicts)
                val resultNumberOfSolutionsVsk = plots.createPlot(
                    "\$k\$",
                    "\$S_{Normalized}(m)\$",
                    "Normalized cumulative number of solutions \$S_{Normalized}(${factorOfRopt}\\%\\cdot R_{opt}) = \\frac{|S_{R\\leq m'}|}{|S|}\$ with minimizing \$m'\\leq ${factorOfRopt}\\%\\cdot R_{opt}\$, such that \$S_{R\\leq m'}\$ exists, in relation to \$k\$ ($parametersFixedStandardDeviation).",
                    "fig:NumberOfSolutionsVsk${s}StandardDeviation${factorOfRopt}PercentageOfRopt",
                    2
                )
                writeOutput(
                    resultNumberOfSolutionsVsk,
                    "NumberOfSolutionsVsk${s}StandardDeviation${factorOfRopt}PercentageOfRopt"
                )
            }
        }
        // Number of solutions versus conflicting transactions
        for (s in minStandardDeviation..maxStandardDeviation step stepStandardDeviation) {
            for (factorOfRopt in listOf(100,120,140,160,180,200)) {
                var plots = ""
                k = minMachines
                i = log2(minMachines.toDouble()).toInt()
                while (k <= maxMachines) {
                    plots += mapOfRuntimes.addCumulativePlotVsConflicts(
                        minConflicts,
                        maxConflicts,
                        stepConflicts,
                        k,
                        s,
                        factorOfRopt
                    )
                    plots += "\$k\$ = ${k}".addLegendEntry()
                    if (stepMachines == 0) {
                        i++
                        k = Math.pow(2.0, i.toDouble()).toInt()
                    } else {
                        k += stepMachines
                    }
                }
                var parametersFixedStandardDeviation =
                    generateParameters(k, k, s, s, minConflicts, maxConflicts)
                val resultNumberOfSolutionsVsk = plots.createPlot(
                    "\$|O|\$ as percentage of \$n\$",
                    "\$S_{Normalized}(m)\$",
                    "Normalized cumulative number of solutions \$S_{Normalized}(${factorOfRopt}\\%\\cdot R_{opt}) = \\frac{|S_{R\\leq m'}|}{|S|}\$ with minimizing \$m'\\leq ${factorOfRopt}\\%\\cdot R_{opt}\$, such that \$S_{R\\leq m'}\$ exists, in relation to number of conflicting transactions ($parametersFixedStandardDeviation).",
                    "fig:NumberOfSolutionsVsConflicts${s}StandardDeviation${factorOfRopt}PercentageOfRopt",
                    2
                )
                writeOutput(
                    resultNumberOfSolutionsVsk,
                    "NumberOfSolutionsVsConflicts${s}StandardDeviation${factorOfRopt}PercentageOfRopt"
                )
            }
        }
    }
}

fun main(args: Array<String>) = CommandLineInterpretation().subcommands(Code(),Solutions(),Normaldistribution(),Charts()).main(args)
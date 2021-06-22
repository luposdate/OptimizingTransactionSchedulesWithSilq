import java.io.File
import java.util.*
import java.util.concurrent.ArrayBlockingQueue
import java.util.concurrent.atomic.AtomicBoolean
import java.util.concurrent.atomic.AtomicLong
import java.util.concurrent.locks.ReentrantLock
import kotlin.concurrent.thread
import kotlin.math.log2

fun permutations(n:Int) = iterator<IntArray> {
    val result = IntArray(n){ -1 }
    val jobs = Stack<IntArray>()
    jobs.push(result)
    while(jobs.isNotEmpty()){
        val job = jobs.pop()
        val remainingTransactions = mutableSetOf<Int>()
        remainingTransactions.addAll(0 until n)
        var i = 0
        while(job[i] >= 0){
            remainingTransactions.remove(job[i])
            i++
        }
        // now create new jobs by filling the next index position in the permutation or emit a complete permutation
        for(t in remainingTransactions){
            val newJob = IntArray(n){ job[it] }
            newJob[i] = t
            if(i == n-1){
                yield(newJob)
            } else {
                jobs.push(newJob)
            }
        }
    }
}

fun machineDistribution(n:Int, k:Int) = iterator<IntArray> {
    if(k > 1){
        val kMinus1 = k-1;
        val result = IntArray(kMinus1) { -1 }
        val jobs = Stack<IntArray>()
        jobs.push(result)
        while(jobs.isNotEmpty()) {
            val job = jobs.pop()
            var i = 0
            while (job[i] >= 0) {
                i++
            }
            val leftLimit = if(i>0) job[i-1] else 0
            for(j in leftLimit until n){
                val newJob = IntArray(kMinus1){ job[it] }
                newJob[i] = j
                if(i == kMinus1-1){
                    yield(newJob)
                } else {
                    jobs.add(newJob)
                }
            }
        }
    } else {
        yield(IntArray(k) { n-1 })
    }
}

inline fun lengthOrConflict(r:Int) = if(r<Int.MAX_VALUE) r.toString() else "conflict!"
inline fun isConflict(r:Int) = r==Int.MAX_VALUE
inline fun isNotConflict(r:Int) = r<Int.MAX_VALUE

inline class Runtimes(val runtimes:TreeMap<Int, AtomicLong>){
    inline fun getTotalNumberOfRuns() = this.runtimes.values.map{ it.toLong() }.sum()

    fun printOut(){
        val total = getTotalNumberOfRuns().toDouble()
        var sum = 0L
        for(entries in this.runtimes){
            sum += entries.value.toLong()
            println("Runtime: ${lengthOrConflict(entries.key)} #:${entries.value} (${100*(entries.value.toDouble()/total)}%) cumulative: $sum (${100*(sum.toDouble()/total)}%)")
        }
    }

    fun toStringForOutput():String {
        var result = ""
        for(entry in this.runtimes){
            result += entry.key.toString() + System.lineSeparator()
            result += entry.value.toString() + System.lineSeparator()
        }
        return result
    }

    fun addCumulativePlotVsRopt():String {
        var result = "\\addplot plot coordinates {" + System.lineSeparator()
        val total = getTotalNumberOfRuns().toDouble()
        val R_opt = this.runtimes.keys.first()
        var sum = 0L
        for(entries in this.runtimes){
            sum += entries.value.toLong()
            if(isNotConflict(entries.key)){
                result += "  (" + (entries.key.toDouble()/R_opt.toDouble()) + ", " + (sum.toDouble()/total) + ")" + System.lineSeparator()
            }
        }
        result += "};" + System.lineSeparator()
        return result;
    }
    fun addAbsoluteCumulativePlotVsRopt():String {
        var result = "\\addplot plot coordinates {" + System.lineSeparator()
        val R_opt = this.runtimes.keys.first()
        var sum = 0L
        for(entries in this.runtimes){
            sum += entries.value.toLong()
            if(isNotConflict(entries.key)){
                result += "  (" + (entries.key.toDouble()/R_opt.toDouble()) + ", " + sum + ")" + System.lineSeparator()
            }
        }
        result += "};" + System.lineSeparator()
        return result;
    }
}

fun HashMap<Triple<Int, Int, Int>, Runtimes>.addCumulativePlotVsK(minMachines:Int, maxMachines:Int, stepMachines:Int, c:Int, s:Int, factorOfRopt:Int):String {
    // factorOfRopt is given in percentage
    var result = "\\addplot plot coordinates {" + System.lineSeparator()
    var k = minMachines
    var i = log2(minMachines.toDouble()).toInt()
    while (k <= maxMachines) {
        val runtimes = this[Triple(k,c,s)]!!
        val total = runtimes.getTotalNumberOfRuns().toDouble()
        val R_opt = runtimes.runtimes.keys.first()
        var sum = 0L
        var flag = true
        for(entries in runtimes.runtimes){
            sum += entries.value.toLong()
            if(isNotConflict(entries.key) && flag){
                val factor = 100.0 * entries.key.toDouble()/R_opt.toDouble()
                if(factor>=factorOfRopt){
                    result += "  ($k, " + (sum.toDouble()/total) + ")" + System.lineSeparator()
                    flag = false
                }
            }
        }
        if (stepMachines == 0) {
            i++
            k = Math.pow(2.0, i.toDouble()).toInt()
        } else {
            k += stepMachines
        }
    }
    result += "};" + System.lineSeparator()
    return result;
}


fun HashMap<Triple<Int, Int, Int>, Runtimes>.addCumulativePlotVsConflicts(minConflicts:Int, maxConflicts:Int, stepConflicts:Int, k:Int, s:Int, factorOfRopt:Int):String {
    // factorOfRopt is given in percentage
    var result = "\\addplot plot coordinates {" + System.lineSeparator()
    for (c in minConflicts..maxConflicts step stepConflicts) {
        val runtimes = this[Triple(k,c,s)]!!
        val total = runtimes.getTotalNumberOfRuns().toDouble()
        val R_opt = runtimes.runtimes.keys.first()
        var sum = 0L
        var flag = true
        for(entries in runtimes.runtimes){
            sum += entries.value.toLong()
            if(isNotConflict(entries.key) && flag){
                val factor = 100.0 * entries.key.toDouble()/R_opt.toDouble()
                if(factor>=factorOfRopt){
                    result += "  ($c, " + (sum.toDouble()/total) + ")" + System.lineSeparator()
                    flag = false
                }
            }
        }
    }
    result += "};" + System.lineSeparator()
    return result;
}


class NumberOfSolutions(val machines: Int, val transactions: List<Int>, val conflicts: List<MutablePair<Int, Int>>) {
    val runtimes = TreeMap<Int, AtomicLong>()
    val lock = ReentrantLock()

    fun runtime(p:IntArray, m:IntArray):Int {
        // for storing the start and end times of transactions in order to detect conflicts of transactions
        val transactionTimes = Array<IntArray>(this.transactions.size){ intArrayOf(0,0) }
        var maxLength=0
        var j = 0
        var l = 0
        for(i in 0 until p.size) {
            transactionTimes[p[i]][0] = l // start time of transaction o[i]
            l += this.transactions[p[i]]
            transactionTimes[p[i]][1] = l // end time of transaction o[i]
            if(i==p.size-1 || (j<m.size && i==m[j])) {
                if(maxLength<l) {
                    maxLength = l
                }
                j++
                l = 0
            }
        }
        for(c in this.conflicts){
            if(!(transactionTimes[c.first][0]>=transactionTimes[c.second][1] || transactionTimes[c.second][0]>=transactionTimes[c.first][1])){
                maxLength = Int.MAX_VALUE
            }
        }
        return maxLength
    }

    fun determineRuntimes(experiments: File? = null):Runtimes {
        println("Lengths of transactions: ${this.transactions}")
        if(experiments!=null && experiments.exists()) {
            // read in and return
            val contents = experiments.readText().split(System.lineSeparator()).filter{ it.compareTo("")!=0 }.map{ it.toLong() }.iterator()
            while(contents.hasNext()){
                val key = contents.next()
                if(contents.hasNext()){
                    val value = contents.next()
                    this.runtimes[key.toInt()] = AtomicLong(value)
                } else {
                    throw Exception("Contents of experiments file is not valid!")
                }
            }
            return Runtimes(this.runtimes)
        }
        val q = ArrayBlockingQueue<IntArray>(100)
        val cores = Runtime.getRuntime().availableProcessors()
        var end:AtomicBoolean = AtomicBoolean(false)
        val producer = thread(start = true) {
            for (p in permutations(this.transactions.size)) {
                q.put(p)
            }
            end.set(true)
        }
        val consumers = Array<Thread>(Math.floor(0.5*cores).toInt()){
            thread(start = true) {
                while(!end.get()){
                    val p = q.poll()
                    if(p!=null){
                        for (m in machineDistribution(this.transactions.size, this.machines)) {
                            val maxLength = runtime(p, m)
                            val count = runtimes[maxLength]
                            if (count == null) {
                                lock.lock()
                                try {
                                    val secondtry = runtimes[maxLength]
                                    if(secondtry==null){
                                        runtimes[maxLength] = AtomicLong(1)
                                    } else {
                                        secondtry.incrementAndGet()
                                    }
                                } finally {
                                    lock.unlock()
                                }
                            } else {
                                count.incrementAndGet()
                            }
                        }
                    }
                }
            }
        }
        producer.join()
        for(t in consumers){
            t.join()
        }
        val result = Runtimes(this.runtimes)
        if(experiments!=null){
            experiments.writeText(result.toStringForOutput())
        }
        return result
    }
}

fun normalDistribution(median:Int, standardDeviation:Int, x:Int) = Math.pow(Math.E,-.5*((x-median).toDouble()/standardDeviation.toDouble())*((x-median).toDouble()/standardDeviation.toDouble())) / (standardDeviation.toDouble()*Math.sqrt(2*Math.PI))

fun transactionLengthsAccordingToNormalDistribution(n:Int, median:Int, standardDeviation:Int):List<Int>{
    val transactions= mutableListOf<Int>()
    for(x in 1 .. 2*median){
        val nrOfTransactionsOfThisLength = normalDistribution(median, standardDeviation, x)*n
        // println("Length: $x #: $nrOfTransactionsOfThisLength")
        val roundedNrOfTransactionsOfThisLength = Math.round(nrOfTransactionsOfThisLength)
        for(i in 0 until roundedNrOfTransactionsOfThisLength){
            transactions.add(x)
        }
    }
    // correct number of transactions (according to observations in very seldom cases only difference of +-1 could occurr)
    while(transactions.size>n){
        transactions.removeAt(Math.floor(Math.random()*transactions.size).toInt())
    }
    while(transactions.size<n){
        transactions.add(median)
    }
    return transactions
}

fun randomConflictingTransactions(n:Int, c:Int):List<MutablePair<Int, Int>> {
    val result = mutableListOf<MutablePair<Int, Int>>()
    while(result.size<c) {
        var first = Math.floor(Math.random()*n).toInt()
        var second = Math.floor(Math.random()*n).toInt()
        if(first!=second) {
            if(first>second) {
                val tmp = first
                first = second
                second = tmp
            }
            val conflict = MutablePair<Int, Int>(first, second)
            if(!result.contains(conflict)){
                result.add(conflict)
            }
        }
    }
    return result
}
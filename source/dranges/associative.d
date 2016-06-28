// Written in the D programming language.
/**
convert AA to range, and merge AA

Authors:    Kazuki Komatsu(k3_kaimu)
License:    NYSL
*/
module dranges.associative;

import dranges.functional;

import std.algorithm,
       std.range,
       std.traits,
       std.typecons;

version(unittest) import std.stdio;


/**
There may be a need for an 'asRange' function that takes a container
and returns a range iterating over the entire content. In this particular case, asRange takes
an associative array of type V[K] and returns (K,V) tuples.
*/
auto asRange(AA)(AA aa)
if(isAssociativeArray!(AA))
{
    static struct AsRange(AA)
    if(isAssociativeArray!(Unqual!AA))
    {
        bool empty() @property
        {
            return _ks.empty;
        }


        auto front() @property
        {
            return tuple(_ks.front, _aa[_ks.front]);
        }


        void popFront()
        {
            _ks.popFront();
        }

      private:
        AA _aa;
        typeof(AA.init.byKey()) _ks;
    }


    return AsRange!AA(aa, aa.byKey);
}

///
unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}
    
    auto aa = ["Hello":5, "World!":6, "a":99, "":0, "Howdy":6];
    auto aa_range = aa.asRange;
    assert(is(ElementType!(typeof(aa_range)) == Tuple!(string, int)));
    assert(equal(aa_range, aa.keys.zip(aa.values)));
}


/// Merge AA, with a merging function if some keys exist on more than one array.
AA merge(alias fn = "c", AA, size_t N)(AA[N] aas...)
if(N >= 2)
{
    AA* l = &(aas[0]),
        s;

    foreach(i; 1 .. N){
        s = &(aas[1]);

        if((*s).length > (*l).length)
            swap(s, l);

        foreach(k, ref v; *s){
            if(k in (*l)){
                auto r = naryFun!fn(k, (*l)[k], v);
                (*l)[k] = r;
            }
            else
                (*l)[k] = v;
        }
    }

    return *l;
}

///
unittest {
    auto aa1 = ["Hello":5, "World!":6],
         aa2 = ["a":99, "":0, "Howdy":6];

    assert(merge(aa1, aa2) == ["Hello":5, "World!":6, "a":99, "":0, "Howdy":6]);
    assert(merge(aa1, typeof(aa2).init) == aa1);
    assert(merge(typeof(aa1).init, aa2) == aa2);

    aa1 = ["Hello":5, "World!":6];
    aa2 = ["Hello":10, "W":2];
    assert(merge!"b+c"(aa1, aa2) == ["Hello":15, "World!":6, "W":2]);
}

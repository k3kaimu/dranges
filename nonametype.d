﻿/**
 * this module, you can create "No Name" union and struct.
 * Example:
 * ---
 * import std.stdio;
 * void main(){
 *     Nuple!(int, 3) a;   //NNUnion!(Tuple!(int, int, int), "nuple", int[3], "array")
 *     
 *     foreach(i; 0..3)
 *         a.array[i] = i * 2;
 *     
 *     writeln(a.array);   //[0, 2, 4]
 *     writeln(a.nuple);   //Tuple!(int, int, int)(0, 2, 4)
 * }
 * ---
 * 
 * Authors:   Kazuki Komatsu(k3kaimu)
 * License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
 */
module dranges.nonametype;

import std.conv             : to;
import std.typecons         : Tuple;

import dranges.typetuple    : TypeNuple;

//create no name struct or union 's member
private string createNNMembers(T...)(){
    string dst;
        
    foreach(i, Unused; T[0..T.length/2]){
        static if(is(typeof((){string a; a ~= T[i*2];})))
        {
            dst ~= T[i*2];
        }
        else
        {
            dst ~= "T[" ~ to!string(i*2) ~ "]";
        }
        dst ~= " " ~ T[i*2+1] ~ ";";
    }
    
    return dst;
}

/**
 * This template create no name union.
 * Example:
 * ---
 * NNUnion!(int[2], "_int", long, "_long") a;
 * 
 * a._int[0] = 12;
 * a._int[1] = 1;
 * assert(a._long == (1L << 32) + 12);
 * ---
 */
template NNUnion(T...)if(T.length && !(T.length&1)){
    mixin("union NNUnion{" ~ createNNMembers!T() ~ "}");
}
unittest{
    NNUnion!(int[2], "_int", long, "_long") a;

    a._int[0] = 12;
    a._int[1] = 1;
    assert(a._long == (1L << 32) + 12);
}


/**
 * This templte create no name struct.
 * Example:
 * ---
 * NNStruct!(string, "str", uint, "value");
 * 
 * a.str = "12";
 * a.value = 1111;
 * ---
 */
template NNStruct(T...)if(T.length && !(T.length&1)){
    mixin("struct NNStruct{" ~ createNNMembers!T() ~ "}");
}
unittest{
    NNStruct!(string, "str", uint, "value") a;

    a.str = "12";
    a.value = 1111;
}


/**
 * This is useful type if you use Tuple!(TypeTuple!(T, N)) in your code. 
 * You can access a tuple element of some one by index.
 * Example:
 * ---
 * Nuple!(int, 3)  npi3;   //union{Tuple!(int, int, int) nuple, int[3] array}
 * 
 * npi3.nuple = tuple(1, 2, 3);
 * 
 * foreach(i; 0..3)
 *     assert(npi3.array[i] == i + 1);
 * --- 
 */
template Nuple(T, size_t N){
    alias NNUnion!(Tuple!(TypeNuple!(T, N)), "nuple", T[N], "array") Nuple;
}
unittest{
    import std.typecons :   tuple;

    Nuple!(int, 3)  npi3;   //union{Tuple!(int, int, int) nuple, int[3] array}

    npi3.nuple = tuple(0, 1, 2);

    foreach(i; 0..3)
        assert(npi3.array[i] == i);
}
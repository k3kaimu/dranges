// Written in the D programming language

/**
This module defines new ranges or rather, higher-order ranges: ranges acting on ranges
to transform them or present a new view. As far as possible, all higher-order ranges presented in this module
and in $(M dranges.algorithm) are "tight wrappers": they are bidirectional if their input range is bidirectional,
define $(M opIndex), $(M opIndexAssign), $(M length) if it's possible, etc. That way, a good input range (for example, a random-access range)
will see its properties propagated through a chain of calls.
$(UL
  $(LI Some of these are usual in other languages (Haskell, Scala, Clojure, ...) and are quite useful: $(M drop), $(M dropWhile), $(M takeWhile), etc.)
  $(LI Some are extension of standard functions: $(M delay) as a generic way to segment a range.)
  $(LI Some are there just for fun and served as exercices when I wanted to "grok" ranges (like $(M torus), $(M bounce), $(M emptyRange), $(M once)).)
  )
Also, once we admit $(M std.typecons.tuples) as a common way to return many values, tuple-returning
ranges can be acted upon in various ways, splicing/shredding/rotating/stitching them. As many ranges and algorithms
presented in this package produce tuples, having a rich way to act upon them permits all kinds of reuse.

License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Philippe Sigaud

Distributed under the Boost Software License, Version 1.0.
(See accompanying file LICENSE_1_0.txt or copy at http://www.boost.org/LICENSE_1_0.txt)
*/
module dranges.range;

import core.thread : Fiber;

import std.algorithm,
       std.array,
       std.bigint,
       std.conv,
       std.exception,
       std.functional,
       std.math,
       //std.metastrings,
       std.range,
       std.stdio,
       std.string,
       std.traits,
       std.typecons,
       std.typetuple;

import dranges.algorithm,
       dranges.functional,
       dranges.predicate,
       dranges.templates,
       dranges.tuple,
       dranges.traits,
       dranges.typetuple,
       dranges.nonametype;

/**
Return:
the smallest length of all non-infinite ranges passed as inputs. All finite ranges must have a length member.
Example:
----
auto s = ["a","b","c","d","e","f"];
int[] r = [0,1,2,3];
auto c = repeat(5); // infinite
auto ml = minLength(s,r,c);
assert(ml == 4); // r length
----
*/
size_t minLength(R...)(R ranges) if (allSatisfy!(isForwardRange, R) && allHaveLength!R && !allAreInfinite!R)
{
    size_t minL = size_t.max;
    foreach(i,Range; R) {
        static if (hasLength!Range) {
            if (ranges[i].length < minL) minL = ranges[i].length;
        }
    }
    return minL;
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto s = ["a","b","c","d","e","f"];
    int[] r = [0,1,2,3];
    auto c = repeat(5); // infinite
    auto ml = minLength(s,r,c);
    assert(ml == 4); // r length
}

/+
auto takeLast(R)(R range, size_t n) if (isBidirectionalRange!R)
{
//    static if (hasSlicing!R && hasLength!R) {
//        if (n > range.length) { n = range.length;}
//        return range[range.length-n .. range.length];
//    }
//    else
        return retro(take(retro(range),n)); // Not exactly right, as take may not be a bidir range
}
+/




/**
To Be Documented.
*/
Take!R slice(R)(R range, int begin, int end)
{
    return take(drop(range, begin), end-begin);
}

/**
Drops the last n elements of range. R must be bidirectional.
*/
R dropLast(R)(R range, size_t n) if (isBidirectionalRange!R)
{
    return retro(drop(retro(range), n));
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4,5];
    auto d = dropLast(r1,3);
    assert(equal(d, [0,1,2][]));
    assert(equal(dropLast(r1,0), r1));
    assert(dropLast(r1,6).empty);
    assert(dropLast(r1,100).empty);
}


/**
Returns a copy of r, with the first elements dropped as long as pred if verified. Compare to
popFrontWhile which affects r.

The predicate may be unary:
----
string s = "  , abcd  efg";
auto d1 = dropWhile!(isOneOf!" ,")(s); // isOneOf!" ," returns true for " " and for ","
assert(d1 == "abcd  efg");

auto r1 = [0,1,2,3,3,4,5];
auto d2 = dropWhile!"a<4"(r1);      // String predicate
assert(equal(d2, [4,5][]));
----

Or it can be binary (or ternary, or whatever), possibly a string, as "a<b".

The second (optional) argment is the step, which must be between 1 and the pred's arity. Step's default is 1.

If step == arity, it will drop the entire segment at each step.

Example:
----
auto d3 = dropWhile!"a<b"(r1);     // drop as long as r1 is strictly increasing, testing with binary predicate "a<b"
                                   // It will test [0,1] and drop 0. Then test [1,2] and drop 1, ...
assert(equal(d3, [3,3,4,5][]));    // the result begins with a couple for which a<b doesn"t hold

auto d4 = dropWhile!("a<b",2)(r1); // drop as long as r1 is strictly increasing, testing with binary predicate, step of 2
                                   // It will test [0,1] and drop [0,1]. Then test [2,3] and drop it also.
                                   // Then it will drop [3,4] and stop at 5.
assert(equal(d4, [5][]));

auto d5 = dropWhile!"a<b && b<c"(r1); // Growing range, with three args (step defaults to 1)
assert(equal(d5, [2,3,3,4,5][]));

bool foo(int a, int b) { return a*b < 3;}
auto d6 = dropWhile!foo(r1);            // binary fun as predicate
assert(equal(d6, [2,3,3,4,5][]));

auto d7 = dropWhile!"true"(r1); // 0-arg predicate, always true -> drops everything -> d7 is empty
assert(d7.empty);

int[] e;
assert(dropWhile!"a<4"(e).empty); // dropping on an empty range: always empty

auto r2 = [1];
auto d8 = dropWhile!"a<b"(r2); // binary predicate: cannot be true applied on [1] -> stops at once
assert(equal(d8, [1][]));

auto d9 = dropWhile!"a < b"(r1, 4);
assert(equal(d9, [4, 5]));
    
auto d10 = dropWhile!"a == b - c"(r1, 1);
assert(equal(d10, [3, 3, 4, 5]));

auto d11 = dropWhile!((a, b, c) => a == b - c)(r1, 1);
assert(equal(d11, [3, 3, 4, 5]));
    
auto d12 = dropWhile!((a, b, c) => a < b, 2)(r1, 1);
assert(equal(d4, [5][]));
----
*/
template dropWhile(alias pred, size_t step = 1){
    alias naryFun!pred predicate;

    template dropWhile(R, T...)if(isForwardRange!R){

        template ParamGenForArity(size_t N){
                alias TypeTuple!(TypeNuple!(ElementType!R, N), T) ParamGenForArity;
        }

        enum N = templateFunctionAnalysis!(predicate, ParamGenForArity).endN;

        R dropWhile(R r, auto ref T subParam)
        {
            static if(N == 0){
                R result = r.save;
                while(!result.empty && predicate(subParam)) result.popFrontN(step);
                return result;
            }else static if(N == 1){
                R result = r.save;
                while(!result.empty && predicate(result.front, subParam)) popFrontN(result, step);
                return result;
            }else{
                R result = r.save;
                auto sr = stride(segment!N(r), step);
                while(!sr.empty && predicate(sr.front.field, subParam)) {
                    sr.popFront;
                    popFrontN(result, step);
                }
                return result;
            }
        }
    }
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

// Unary predicate tests:
    string s = "  , abcd  efg";
    auto d1 = dropWhile!(a => a.isOneOf(" ,"))(s);
    assert(d1 == "abcd  efg");

    auto r1 = [0,1,2,3,3,4,5];
    auto d2 = dropWhile!"a<4"(r1);      // String predicate
    assert(equal(d2, [4,5][]));
    
    assert(equal(dropWhile!("a<4",1)(r1), dropWhile!"a<4"(r1))); // Unary pred: you can tell dropWhile it's unary...

// N-ary predicate tests:
    auto d3 = dropWhile!("a<b")(r1);  // drop as long as r1 is strictly increasing, testing with binary predicate "a<b"
                                        // It will test [0,1] and drop 0. Then test [1,2] and drop 1, ...
    assert(equal(d3, [3,3,4,5][]));     // the result begins with a couple for which a<b doesn"t hold

    auto d4 = dropWhile!("a<b",2)(r1);// drop as long as r1 is strictly increasing, testing with binary predicate, step of 2
                                        // It will test [0,1] and drop [0,1]. Then test [2,3] and drop it also.
                                        // Then it will drop [3,4] and stop at 5.
    assert(equal(d4, [5][]));

    auto d5 = dropWhile!("a<b && b<c")(r1); // Growing range, with three args (step defaults to 1)
    assert(equal(d5, [2,3,3,4,5][]));

    bool foo(int a, int b) { return a*b < 3;}
    auto d6 = dropWhile!foo(r1);            // binary fun as predicate
    assert(equal(d6, [2,3,3,4,5][]));

    auto d7 = dropWhile!"true"(r1); // 0-arg predicate, always true -> drops everything -> d7 is empty
    assert(d7.empty);

    auto d7_d = dropWhile!("true", 2)(r1);
    assert(d7_d.empty);

    int[] e;
    assert(dropWhile!"a<4"(e).empty); // dropping on an empty range: always empty

    auto r2 = [1];
    auto d8 = dropWhile!"a<b"(r2); // binary predicate: cannot be true aplied on [1] -> stops at once
    assert(equal(d8, [1][]));
    
    auto d9 = dropWhile!"a < b"(r1, 4);
    assert(equal(d9, [4, 5]));
    
    auto d10 = dropWhile!"a == b - c"(r1, 1);
    assert(equal(d10, [3, 3, 4, 5]));
    
    auto d11 = dropWhile!((a, b, c) => a == b - c)(r1, 1);  //lambda OK
    assert(equal(d11, [3, 3, 4, 5]));
    
    auto d12 = dropWhile!((a, b, c) => a < b, 2)(r1, 1);    //lambda and step OK
    assert(equal(d12, [5][]));
    
    auto d13 = dropWhile!(a => a < 4)(r1);
    assert(equal(d13, [4,5][]));
    
    auto d14 = dropWhile!(() => true)(r1);
    assert(d14.empty);
    auto d15 = dropWhile!(() => false)(r1);
    assert(equal(d15, r1));

    size_t cnt;
    bool counter(){return cnt++ < 3;}

    auto d16 = dropWhile!(counter)(r1);
    assert(equal(d16, [3, 3, 4, 5]));
}

/**
Advances range while predicate pred is true. It will change range!
The predicate can be a function or a string. If it's a binary (or more) predicate,
it will test as many elements (2, 3...) in one step.

There is an optional argument: the step, defaulting to 1.
Returns: the number of elements popped.
See_Also: dropWhile.
Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = [0,1,2,3,4];
auto r3 = [0,1,2,1,0];
auto r4 = [0,1,2,3,2,1];
auto e;

auto a = popFrontWhile!"a<2"(r1); // standard use
assert(equal(r1, [2,3,4][]));
assert(a == 2);

a = popFrontWhile!"a>5"(r2);
assert(equal(r2, [0,1,2,3,4][])); // false predicate, nothing changed
assert(a == 0);

a = popFrontWhile!"a<b"(r3); // binary predicate, step defaults to 1.
assert(equal(r3, [2,1,0][]));
assert(a == 2);

a = popFrontWhile!("a<b",2)(r4); // binary predicate, step of 2.
assert(equal(r4, [2,1][]));
assert(a == 4);

a = popFrontWhile!"a>5"(e); // On an empty range, pops nothing.
assert(a == 0);
----
*/
template popFrontWhile(alias pred, size_t step = 1){
    alias naryFun!pred predicate;
    
    template popFrontWhile(R, T...){
        
        template ParamGenForArity(size_t N){
            alias TypeTuple!(TypeNuple!(ElementType!R, N), T) ParamGenForArity;
        }
        
        enum N = templateFunctionAnalysis!(predicate, ParamGenForArity).endN;
        alias ElementType!R ET;
        
        size_t popFrontWhile(ref R r, T subArgs){
            
            static if(N == 0){
                size_t pops;
                while(!r.empty && predicate(subArgs))
                    pops += r.popFrontN(step);
                
                return pops;
            }else static if(N == 1){
                size_t pops;
                while(!r.empty && predicate(r.front, subArgs))
                    pops += r.popFrontN(step);
                    
                return pops;
            }else{
                static assert(isForwardRange!R, "if arity!pred > 1, input of popFrontWhile is needed a ForwardRange.");
                size_t pops;
                auto sr = stride(segment!N(r), step);
                while(!r.empty && predicate(sr.front.field, subArgs)){
                    sr.popFront;
                    pops += r.popFrontN(step);
                }
                return pops;
            }
        }
    }
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4];
    auto r2 = [0,1,2,3,4];
    auto r3 = [0,1,2,1,0];
    auto r4 = [0,1,2,3,2,1];
    int[] e;

    auto a = popFrontWhile!"a<2"(r1);
    assert(equal(r1, [2,3,4][]));
    assert(a == 2);
    r1 = r2.dup;
    a = popFrontWhile!(a => a < 2)(r1);
    assert(equal(r1, [2,3,4][]));
    assert(a == 2);
    r1 = r2.dup;
    
    a = popFrontWhile!"a>5"(r2);
    assert(equal(r2, [0,1,2,3,4][])); // false predicate, nothing changed
    assert(a == 0);
    r2 = r1.dup;
    a = popFrontWhile!((a, b) => a > b)(r2, 5);
    assert(equal(r2, [0,1,2,3,4][]));
    assert(a == 0);

    a = popFrontWhile!"a<b"(r3); // binary predicate, step defaults to 1.
    assert(equal(r3, [2,1,0][]));
    assert(a == 2);

    a = popFrontWhile!("a<b", 2)(r4); // binary predicate, step of 2.
    assert(equal(r4, [2,1][]));
    assert(a == 4);

    a = popFrontWhile!"a>5"(e); // On an empty range, pops nothing.
    assert(a == 0);
}

/**
Takes elements from range as long as pred is verified. Usually, the predicate
is a unary function. It can be a binary (or more) function, but only the first element is delivered.
Compared to dropWhile and such, there is no step option.
Example:
----
auto r1 = [0,1,2,3,4,4,6,1,1,1,0];
auto tw1 = takeWhile!"a<6"(r1); // unary predicate
assert(equal(tw1, [0,1,2,3,4,4][]));
auto tw2 = takeWhile!"a<b"(r1); // binary predicate
assert(equal(tw2, [0,1,2,3][]));
bool foo(int a, int b, int c) {return a<b && b<c;} // ternary predicate
auto tw3 = takeWhile!foo(r1);
assert(equal(tw3, [0,1,2][]));
auto tw4 = takeWhile!"true"(r1); // 0-arg predicate (seems silly, but may be generated by a template)
assert(equal(tw4, r1));
auto tw5 = takeWhile!"false"(r1);
assert(tw5.empty);
auto tw6 = takeWhile!"a < b"(r1, 6);    //b is 6
assert(equal(tw6, [0, 1, 2, 3, 4, 4]));
auto tw7 = takeWhile!"a == (b - c)"(r1, 1); //a and b are range elements. c is 1
assert(equal(tw7, [0, 1, 2, 3]));
    
int[] e;
assert(takeWhile!"a > b"(e).empty); // takeWhile on an empty range -> empty
----
*/
template takeWhile(alias pred){
    alias naryFun!pred predicate;
    
    template takeWhile(R, T...)if(isForwardRange!R)
    {
        TakeWhile takeWhile(R range, T args){
            return TakeWhile(range, args);
        }
        
        template ParamGenForArity(size_t N){
            alias TypeTuple!(TypeNuple!(ElementType!R, N), T) ParamGenForArity;
        }
        
        struct TakeWhile{
            Tuple!T _subArgs;
            
            enum N = templateFunctionAnalysis!(predicate, ParamGenForArity).endN;
            
            static if(N)
                SegmentType!(N, R) _sr;
            else
                R _sr;
            
            this(R range, T subArgs){
                _subArgs = tuple(subArgs);
                
                static if(N)
                    _sr = segment!N(range.save);
                else
                    _sr = range.save;
            }
            
            @property
            bool empty(){
                static if(!N){
                    return _sr.empty || !predicate(_subArgs.field);
                }else{
                    return _sr.empty || !predicate(_sr.front.field, _subArgs.field);
                }
            }
            
            @property
            ElementType!R front(){
                static if(N)
                    return _sr.front[0];
                else
                    return _sr.front;
            }
            
            void popFront(){
                _sr.popFront();
            }
            
            @property
            TakeWhile save(){
                TakeWhile dst = this;
                dst._sr = _sr.save;
                return dst;
            }
        }
    }
}

///ditto
template multiTakeWhile(pred...)if(pred.length){
    alias staticMap!(naryFun, pred) predicates;
    
    template multiTakeWhile(R, T...)if(isForwardRange!R)
    {
        MultiTakeWhile multiTakeWhile(R range, T args){
            return MultiTakeWhile(range, args);
        }
        
        template ParamGenForArity(size_t N){
            alias TypeTuple!(TypeNuple!(ElementType!R, N), T) ParamGenForArity;
        }
        
        template MaxOf(Expr...)if(Expr.length){
            static if(Expr.length == 1)
                enum MaxOf = Expr[0];
            else{
                enum MaxOf = Expr[0] > MaxOf!(Expr[1..$]) ? Expr[0] : MaxOf!(Expr[1..$]);
            }
        }
        
        template segmentAritys(size_t predIdx){
            static if(predIdx < pred.length){
                alias predicates[predIdx] pred;
                
                
                alias TypeTuple!(templateFunctionAnalysis!(pred, ParamGenForArity).endN, segmentAritys!(predIdx+1)) segmentAritys;
            }else
                alias TypeTuple!() segmentArity;
        }
        
        struct MultiTakeWhile{
            Tuple!T _subArgs;
            
            alias segmentAritys!(0)[0..pred.length] Ns;
            enum N = MaxOf!(Ns);
            
            static if(N)
                Segment!(R, N) _sr;
            else
                R _sr;
            
            this(R range, T subArgs){
                _subArgs = tuple(subArgs);
                
                static if(N)
                    _sr = segment!N(range.save);
                else
                    _sr = range.save;
            }
            
            @property
            bool empty(){
                foreach(i, Ne; Ns){
                    static if(!Ne){
                        if(_sr.empty || !predicates[i](_subArgs.field))
                            return true;
                    }else{
                        if(_sr.empty || !predicates[i](_sr.front.field[0..Ne], _subArgs.field))
                            return true;
                    }
                }
                return false;
            }
            
            @property
            ElementType!R front(){
                static if(N)
                    return _sr.front[0];
                else
                    return _sr.front;
            }
            
            void popFront(){
                _sr.popFront();
            }
            
            @property
            MultiTakeWhile save(){
                MultiTakeWhile dst = this;
                dst._sr = _sr.save;
                return dst;
            }
        }
    }
}
/*


/// ditto
TakeWhile!(pred, R, AT) takeWhile(alias pred, R, AT...)(R range, AT args) if (isForwardRange!R)
{
    return TakeWhile!(pred, R, AT)(range, args);
}
*/

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0, 1, 2, 3, 4, 4, 6, 1, 1, 1, 0];
    auto tw1 = takeWhile!"a < 6"(r1); // unary predicate
    assert(equal(tw1, [0,1,2,3,4,4][]));
    auto tw2 = takeWhile!"a < b"(r1); // binary predicate
    assert(equal(tw2, [0,1,2,3][]));
    bool foo(int a, int b, int c) {return a<b && b<c;} // ternary predicate
    auto tw3 = takeWhile!foo(r1);
    assert(equal(tw3, [0,1,2][]));
    auto tw4 = takeWhile!"true"(r1); // 0-arg predicate (seems silly, but may be generated by a template)
    assert(equal(tw4, r1));
    auto tw5 = takeWhile!"false"(r1);
    assert(tw5.empty);
    auto tw6 = takeWhile!"a < b"(r1, 6);    //b is 6
    assert(equal(tw6, [0, 1, 2, 3, 4, 4]));
    auto tw7 = takeWhile!"a == (b - c)"(r1, 1); //a and b are range elements. c is 1
    assert(equal(tw7, [0, 1, 2, 3]));
    auto tw8 = takeWhile!((a, b, c) => a == (b - c))(r1, 1);
    assert(equal(tw8, [0, 1, 2, 3]));
    
    int[] e;
    assert(takeWhile!"a > b"(e).empty); // takeWhile on an empty range -> empty
}

/**
Until the advent of such an element satisfies the condition.
*/
template takeUntil(alias pred)
{
    alias naryFun!pred predicate;
    
    template takeUntil(R, T...)if(isForwardRange!R)
    {
        TakeUntil takeUntil(R range, T args){
            return TakeUntil(range, args);
        }
        
        template ParamGenForArity(size_t N){
            alias TypeTuple!(TypeNuple!(ElementType!R, N), T) ParamGenForArity;
        }
        
        struct TakeUntil{
            Tuple!T _subArgs;
            
            enum N = templateFunctionAnalysis!(predicate, ParamGenForArity).endN;
            
            static if(N)
                SegmentType!(N, R) _sr;
            else
                R _sr;
            
            this(R range, T subArgs){
                _subArgs = tuple(subArgs);
                
                static if(N)
                    _sr = segment!N(range.save);
                else
                    _sr = range.save;
            }
            
            @property
            bool empty(){
                static if(!N){
                    return _sr.empty || predicate(_subArgs.field);
                }else{
                    return _sr.empty || predicate(_sr.front.field, _subArgs.field);
                }
            }
            
            @property
            ElementType!R front(){
                static if(N)
                    return _sr.front[0];
                else
                    return _sr.front;
            }
            
            void popFront(){
                _sr.popFront();
            }
            
            @property
            TakeUntil save(){
                TakeUntil dst = this;
                dst._sr = _sr.save;
                return dst;
            }
        }
    }
}

unittest{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0, 1, 2, 3, 4, 4, 6, 1, 1, 1, 0];
    auto tw1 = takeUntil!"a >= 6"(r1); // unary predicate
    assert(equal(tw1, [0,1,2,3,4,4][]));
    auto tw2 = takeUntil!"a >= b"(r1); // binary predicate
    assert(equal(tw2, [0,1,2,3][]));

    bool foo(int a, int b, int c){return a<b && b<c;} // ternary predicate

    auto tw3 = takeUntil!foo(r1);
    assert(tw3.empty);
    auto tw4 = takeUntil!"false"(r1); // 0-arg predicate (seemse silly, but may be generated by a template)
    assert(equal(tw4, r1));
    auto tw5 = takeUntil!"true"(r1);
    assert(tw5.empty);
    
    auto tw6 = takeUntil!"a >= b"(r1, 6);    //b is 6
    assert(equal(tw6, [0, 1, 2, 3, 4, 4]));
    auto tw7 = takeUntil!"a != (b - c)"(r1, 1); //a and b are range elements. c is 1
    assert(equal(tw7, [0, 1, 2, 3]));
    auto tw8 = takeUntil!((a, b, c) => a != (b - c))(r1, 1);
    assert(equal(tw8, [0, 1, 2, 3]));
    
    int[] e;
    assert(takeUntil!"a > b"(e).empty); // takeWhile on an empty range -> empty
}

/**
rotateWhile
*/
template rotateWhile(alias pred){
    alias naryFun!pred predicate;
    
    template rotateWhile(R, T...)if(isForwardRange!R){
        RotateWhile rotateWhile(R range, T args){
            return RotateWhile(range, args);
        }
    }
}

/**
Like the eponymous function found in all functional languages.
Returns the range minus its first element. If range is empty
it just returns it.
Example:
----
auto r = [0,1,2,3];
auto tails = [r][];
foreach(i; 0..5) {
    r = tail(r);
    tails ~= r;
}
assert(equal(tails, [[0,1,2,3], [1,2,3], [2,3], [3], [], [] ][]));
----
*/
R tail(R)(R range) if (isInputRange!R)
{
    if (!range.empty) range.popFront;
    return range;
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r = [0,1,2,3];
    auto tails = [r][];
    foreach(i; 0..5) {
        r = tail(r);
        tails ~= r;
    }
    assert(equal(tails, [[0,1,2,3], [1,2,3], [2,3], [3], [], [] ][]));
}


// helper function for tails
Tuple!(R, R, bool) nextTail(R)(R range, bool empt = false) if (isInputRange!R)
{
    auto t = tail(range);
    return tuple(t, t, range.empty);
}

// helper function for tails. Needed to get DMD happy with the predicate type.
// unfold2!(nextTail!R, "c")(range, false) works perfectly well,
// but the compiler does not like the corresponding return type
bool isE(R)(R r, R r2, bool empt) { return empt;}

/**
Returns the successive application of tail on a range, up to the empty range.
If the input range is empty, tails is empty.
Example:
----
auto r = [0,1,2,3];
auto t = tails(r);
assert(equal(t, [[1,2,3], [2,3], [3], [] ][]));

int[] e;
auto t1 = tails(r[0..1]);
assert(equal(t1, [e][])); // One element -> [] and then stops.

auto te = tails(e);
assert(te.empty); // No element -> empty
----
*/

Tails!R tails(R)(R range) if (isForwardRange!R)
{
    return unfold2!(nextTail!R, isE!R)(range, false);
}

template Tails(R) if (isForwardRange!R)
{
    alias Unfold2!(nextTail!R, isE!R, R, bool) Tails;
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r = [0,1,2,3];
    auto t = tails(r);
    assert(equal(t, [[1,2,3], [2,3], [3], [] ][]));

    int[] e;                  // empty range
    auto t1 = tails(r[0..1]); // One element range
    assert(equal(t1, [e][])); // One element -> [] and then stops.

    auto te = tails(e);
    assert(te.empty); // No element -> empty
}


/**
Takes n successive elements from range, with n going from 0 (an empty range) to range.length included.
It's more efficient for a range with a length: heads knows when to stop. For a range
that doesn"t know its length, heads has to calculate for each new head if it's the entire range.
Example:
----
auto r = [0,1,2,3];
auto h = heads(r);
assert(equal(h, [[], [0], [0,1], [0,1,2], [0,1,2,3] ][])); // from [] up to r itself.

auto f = filter!"a<10"(r); // equivalent to r, but doesn"t know its own length
auto hf = heads(f);
foreach(elem; hf) { // Compare it to f
    assert(equal(elem, h.front)); // They are indeed the same
    h.popFront;
    l++; // accumulate length
}
popFrontN(hf, l); // get rid of all elements?
assert(hf.empty); // Yes, it's empty
----
*/
auto heads(R)(R range) if (isForwardRange!R)
{
    static if (hasLength!R)
        return range.repeat().zip(numberz(range.length+1)).map!(a => take(a[0], a[1]));
    else
        return HeadsStruct!R(range);
}

template Heads(R) if (isForwardRange!R)
{
    alias Heads = typeof(heads(R.init));
}

struct HeadsStruct(R) if (isForwardRange!R && !hasLength!R)
{
    R _range;
    size_t n;
    this(R range) { _range = range;}
    @property bool empty() {
        return (n>0 && drop(n-1,_range).empty && drop(n,_range).empty);
    }
    @property Take!R front() { return take(_range, n);}
    @property HeadsStruct save() { return this;}
    void popFront() {n++;}
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r = [0,1,2,3];
    auto h = heads(r);
    auto witness = [ [], [0], [0,1], [0,1,2], [0,1,2,3] ][];
    foreach(elem; h) {
        assert(equal(elem, witness.front));
        witness.popFront;
    }

    auto f = filter!"a<10"(r); // does not know its own length
//    auto hf = heads(f);
    size_t l;
//    foreach(elem; hf) { // Compare it to f
//        assert(equal(elem, h.front));
//        h.popFront;
//        l++; // accumulate length
//    }
//    popFrontN(hf, l); // get rid of all elements?
//    assert(hf.empty); // Yes, it's empty
}

/**
Inserts an element or an entire range into range1 at position n. Position 0 means before range1. If position >= range1.length,
element/range2 is just concatenated at the end.
Examples:
----
auto r1 = [0,1,2,3];
auto m = map!"a*a"(r1);

auto ia0 = insertAt(0, r1, m);
auto ia2 = insertAt(2, r1, m);
auto ia10 = insertAt(10, r1, m);

assert(equal(ia0, [0,1,4,9,  0,1,2,3][]));
assert(equal(ia2, [0,1,  0,1,4,9,  2,3][]));
assert(equal(ia10,[0,1,2,3,  0,1,4,9][]));

auto ia1 = insertAt(1, r1, 99);
assert(equal(ia1, [0,99,1,2,3][]));
----
*/
auto insertAt(R1, R2)(size_t n, R1 range1, R2 range2) if (allSatisfy!(isForwardRange, R1, R2))
{
    return chain(take(range1, n), range2, drop(range1, n));
}

/// ditto
auto insertAt(R, E)(size_t n, R range, E element) if (isForwardRange!R && is(ElementType!R == E))
{
    return chain(take(range, n), [element][], drop(range, n));
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3];
    auto m = map!"a*a"(r1);
    auto ia0 = insertAt(0, r1, m);
    auto ia2 = insertAt(2, r1, m);
    auto ia10 = insertAt(10, r1, m);
    assert(equal(ia0, [0,1,4,9,  0,1,2,3][]));
    assert(equal(ia2, [0,1,  0,1,4,9,  2,3][]));
    assert(equal(ia10,[0,1,2,3,  0,1,4,9][]));

    auto ia1 = insertAt(1, r1, 99);
    assert(equal(ia1, [0,99,1,2,3][]));
}

/**
Cuts a range in two parts, separating them at _index index. It returns the parts as a tuple.
The second part will begin with range[index].
If slicing is available, it will use it and return a Tuple!(R,R). If not, it iterates the range
and returns a Tuple!( (ElementType!R)[], R ).
----
auto r1 = [0,1,2,3,4,5]; // Cutting an array (range with length and slicing)
auto c1 = cutAt(3, r1);
assert(first(c1) == [0,1,2][]);     // first part
assert(second(c1) == [3,4,5][]);    // second part
assert(equal(r1, [0,1,2,3,4,5][])); // r1 is unchanged
auto c2 = cutAt(0, r1);             // Cuts at position 0
assert(first(c2).empty);
assert(second(c2) == r1);
auto c3 = cutAt(1000, r1);          // Cuts farther than range.length. No exception is thrown, it returns (range, [])
assert(first(c3) == r1);
assert(second(c3).empty);
auto c4 = cutAt(5, stutter(3, r1)); // Cutting a range with a length but no slicing
assert(equal(first(c4), [0,0,0,1,1][]));
assert(is(typeof(first(c4)) == int[]));           // The first part is an int[] (nothing more can be done generically)
assert(equal(second(c4), [1,2,2,2,3,3,3,4,4,4,5,5,5][]));
assert(is(typeof(second(c4)) == Stutter!(int[]))); // The second part is still a Stutter
----
*/
Tuple!(R, R) cutAt(R)(size_t index, R range) if (isForwardRange!R && hasSlicing!R && hasLength!R)
{
    if (index > range.length) index = range.length;
    return tuple(range[0 .. index], range[index .. range.length]);
}

/// ditto
Tuple!(ElementType!R[], R) cutAt(R)(size_t index, R range) if (isForwardRange!R && (!hasSlicing!(R) || !hasLength!(R)))
{
    ElementType!R[] firstPart;
    R secondPart = range;
    foreach(i; 0 .. index) {
        if (secondPart.empty) break;
        firstPart ~= secondPart.front();
        secondPart.popFront();
    }
    return tuple(firstPart, secondPart);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4,5]; // Cutting an array (range with length and slicing)
    auto c1 = cutAt(3, r1);
    assert(first(c1) == [0,1,2][]);     // first part
    assert(second(c1) == [3,4,5][]);    // second part
    assert(equal(r1, [0,1,2,3,4,5][])); // r1 is unchanged
    auto c2 = cutAt(0, r1);             // Cuts at position 0
    assert(first(c2).empty);
    assert(second(c2) == r1);
    auto c3 = cutAt(1000, r1);          // Cuts farther than range.length. No exception is thrown, it returns (range, [])
    assert(first(c3) == r1);
    assert(second(c3).empty);

    auto c4 = cutAt(5, stutter(3, r1)); // Cutting a range with a length but no slicing
    assert(equal(first(c4), [0,0,0,1,1][]));
    assert(is(typeof(first(c4)) == int[]));           // The first part is an int[] (nothing more can be done generically)
    assert(equal(second(c4), [1,2,2,2,3,3,3,4,4,4,5,5,5][]));
    assert(is(typeof(second(c4)) == Stutter!(int[]))); // The second part is still a Stutter

    // Cutting an empty range
    int[] e;
    auto c5 = cutAt(4, e); // Cutting an empty range results in two empty ranges of same nature
    assert(first(c5).empty);
    assert(is(ElementType!(typeof(first(c5))) == int));
    assert(second(c5).empty);
    assert(is(ElementType!(typeof(second(c5))) == int));
}

/**
Iterates on range as long as pred(elem) is verified. Then returns a tuple containing the first part as an array
and the second part as a truncated range.

Note: It cannot return a Tuple!(R,R) as sometimes we cannot construct a R from the popped elements: if
R is a Map!() for example, there is no easy and generic way for the first part to be created as a Map also.

Example:
----
auto r1 = [0,1,2,3,4];
auto cut = cutWhen!"a<3"(r1);
assert(equal(cut.field[0], [0,1,2][]));
assert(equal(cut.field[1], [3,4][]));

assert(equal(r1, [0,1,2,3,4][])); // r1 is unchanged
----
*/
Tuple!(ElementType!(R)[], R) cutWhen(alias pred, R)(R range) if (isForwardRange!R)
{
    alias unaryFun!(pred) predicate;
    ElementType!(R)[] firstPart;
    R secondPart = range;
    while (!range.empty && predicate(secondPart.front)) {
        firstPart ~= secondPart.front();
        secondPart.popFront();
    }
    return Tuple!(ElementType!(R)[], R)(firstPart, secondPart);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4];
    auto cut = cutWhen!"a<3"(r1);
    assert(equal(cut.field[0], [0,1,2][]));
    assert(equal(cut.field[1], [3,4][]));

    assert(equal(r1, [0,1,2,3,4][])); // r1 is unchanged
}


/**
An alternate (simpler) form of std.range.zip: produce a range of std.typecons.Tuples from
a variadic list. Used mainly to interact with other ranges, as Tuples are more generic
than Proxy. It will stops as soon as one of the input ranges is empty.
If only one range is given as input, it will still produce a tuple. So knit(r) != r

It's an extensible range: opIndex, back, popBack, length, opIndex, opIndexAssign and opSlice
are defined if possible (though some improvement could be made on dealing with infinite ranges).
If all ranges are infinite, Knit sees it and defines itself as infinite also.

Note:
it unqualifies the element types (ie: a string has immutable(char) for element type,
but the tuple will use only char).

Example:
----
auto r1 = [0,1,2,3,4,5];
auto r2 = [3.14, 2.78, 0.25, -1.0, 0.0];
auto s = ["a","b","c","d"];

auto k = knit(r1,s,r2);
assert(k.front == tuple(0,"a",3.14));
assert(equal(k, [tuple(0,"a",3.14), tuple(1,"b",2.78), tuple(2,"c",0.25), tuple(3,"d",-1.0)][]));

// Defining more operations:
assert(k.length == s.length); // length is defined
// back and popBack are defined
assert(equal(retro(k),
            [tuple(3,"d",-1.0), tuple(2,"c",0.25), tuple(1,"b",2.78), tuple(0,"a",3.14)][]));
assert(k[2] == tuple(2, "c", 0.25)); // opIndex is defined
assert(equal(k[1..3], [tuple(1, "b", 2.78), tuple(2, "c", 0.25)][])); // opSlice is defined

// More operations impossible:
auto m = map!"a*a"(r2); // no .length, .back, ... (except if you use phobos_extension.d)
auto k2 = knit(r1, r2, m);
assert(k2.front == tuple(0, 3.14, 3.14*3.14));
assert(!is(typeof(k2.length))); // so no .length defined for k2. Nor .back, etc.

// OpIndexAssign: needs ranges which are assignable (ie: no string, map...)
auto k3 = knit(r1, r2);
k3[2] = tuple(0, 0.0);
assert(equal(k3, [tuple(0, 3.14), tuple(1,2.78), tuple(0,0.0), tuple(3, -1.0), tuple(4, 0.0)][]));

// On empty ranges: empty
assert(knit(r1, emptyRange!int, r2).empty);
----
Limitation:
It cannot be sorted, as front/back do not return by ref. std.range.Zip sort of cheats, inserting a
special proxySwap method inside its Proxy, which is treated specially by std.algo.sortImpl. If you
need a Knit to be sorted, you can call sortAsArray on it.
Example:
----
auto ak = sortAsArray(k);
----
*/
/*
struct Knit(Ranges...)
if(Ranges.length && allSatisfy!(isInputRange, staticMap!(Unqual, Ranges)))
{
    alias staticMap!(Unqual, Ranges) R;
    Tuple!R _ranges;
    alias Tuple!(staticMap!(ElementType, R)) FrontTuple;

    this(R ranges) {
        foreach(i, Unused; R)
            _ranges[i] = ranges[i];
        
        static if (allHaveLength!R && !allAreInfinite!R && allSatisfy!(hasSlicing, R))
            truncate(_ranges.field);
    }

    static if (allAreInfinite!R) {
        enum bool empty = false; // Then Knit is also infinite
    }
    else {
        @property
        bool empty() {
            return someEmpty(_ranges.field);
        }
    }
    
    @property
    FrontTuple front() {
        FrontTuple f;
        foreach(i, Unused; R) 
            f.field[i] = _ranges[i].front;
        
        return f;
    }
    
    static if(allSatisfy!(hasAssignableElements, R))
    @property
    void front(FrontTuple tp){
        foreach(i, Unused; FrontTuple.Types)
            _ranges[i].front = tp.field[i];
    }
    
    static if(allSatisfy!(isForwardRange, R))
        @property Knit save() {
            Knit dst = this;
            foreach(i, Unused; R)
                dst._ranges[i] = dst._ranges[i].save;
            return dst;
        }

    void popFront() {
        foreach(i, Unused; R) {
            _ranges[i].popFront;
        }
    }

    static if (allSatisfy!(isRandomAccessRange, R)) {
        FrontTuple opIndex(size_t n) {
            FrontTuple result;
            foreach(i, Unused; R) {
                result.field[i] = _ranges[i][n];
            }
            return result;
        }

        static if (allSatisfy!(hasAssignableElements, R)) {
            void opIndexAssign(FrontTuple ft, size_t n) {
                foreach(i, Unused; R) {
                    _ranges[i][n] = ft.field[i];
                }
            }
        }
    }

    

    static if(allSatisfy!(hasSlicing, R)) {
        Knit!R opSlice(size_t index1, size_t index2) {
            string createSlice(){
                string dst;
                foreach(i, Unused; R)
                    dst ~= "_ranges" ~ "[" ~ i.to!string ~ "][index1..index2],";
                return dst[0..$-1];
            }
            
            return mixin("knit(" ~ createSlice() ~ ")");
        }
    }

    static if(allHaveLength!(R) && !allAreInfinite!(R)){
        @property
        size_t length(){
            return minLength(_ranges.field);
        }
    }

    static if(allHaveLength!(R) && !allAreInfinite!(R) && allSatisfy!(hasSlicing, R)) {
        static if (allSatisfy!(isBidirectionalRange, R)) {
            @property
            FrontTuple back() {
                FrontTuple f;
                foreach(i, Unused; R) {
                    f.field[i] = _ranges[i].back;
                }
                return f;
            }

            static if (allSatisfy!(hasAssignableElements, R)) {
                @property
                void back(FrontTuple ft){
                    foreach(i, Unused; R) {
                        _ranges[i].front = ft.field[i];
                    }
                }
            }

            void popBack() {
                foreach(i, Unused; R) {
                    _ranges[i].popBack;
                }
            }
        }
    }

//    mixin Chainable!();
}


Knit!(R) knit(R...)(R ranges) if (allSatisfy!(isInputRange, R))
{
    return Knit!(R)(ranges);
}*/


//template Knit(R...)if(is(typeof(knit(R.init)))){
//    alias typeof(knit(R.init)) Knit;
//}

//auto knit(R...)(R ranges)if(R.length > 0 && (R.length == 1 ? is(typeof(map!"tuple(a)"(R.init))) : is(typeof(zip(R.init)))))
//{
//    //static if (allHaveLength!R && !allAreInfinite!R && allSatisfy!(hasSlicing, R))
//    //    truncate(ranges);
//    return zip(ranges);
//}

alias knit = std.range.zip;
alias Knit(R...) = typeof(zip(R.init));

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4,5];
    auto r2 = [3.14, 2.78, 0.25, -1.0, 0.0];
    auto s = ["a","b","c","d"];

    auto k = knit(r1,s, r2);
    assert(k.front == tuple(0,"a", 3.14));
    assert(equal(k, [tuple(0,"a", 3.14), tuple(1, "b", 2.78), tuple(2, "c", 0.25), tuple(3, "d", -1.0)][]));

    //assert(k._ranges[1] == s);

// Defining more operations:
    assert(k.length == s.length); // length is defined
    //assert(equal(retro(k), [tuple(3,"d", -1.0), tuple(2, "c", 0.25), tuple(1, "b", 2.78), tuple(0, "a", 3.14)][])); // back and popBack are defined
    assert(k[2] == tuple(2, "c", 0.25)); // opIndex is defined
    assert(equal(k[1..3], [tuple(1, "b", 2.78), tuple(2, "c", 0.25)][])); // opSlice is defined
    assert(k[0..0].empty);

// More operations impossible:
    auto m = map!"a*a"(r2); // no .length, .back, ...
    auto k2 = knit(r1, r2, m);
    assert(k2.front == tuple(0, 3.14, 3.14*3.14));
//    assert(!is(typeof(k2.length))); // so no .length defined for k2. Nor .back, etc.
    // Would Map have a length, back and such, k2 would have them also.

// OpIndexAssign: needs ranges which are assignable (ie: no string, map...)
    auto k3 = knit(r1, r2);
    k3[2] = tuple(0, 0.0);
    assert(equal(k3, [tuple(0, 3.14), tuple(1,2.78), tuple(0,0.0), tuple(3, -1.0), tuple(4, 0.0)][]));

// On empty ranges: empty
    int[] e;
    assert(knit(r1, e, r2).empty);
}

/**
Create a tuple-returning range from a variadic list of tuple-returning ranges by outputting their elements
all in parallel in one tuple.
(it's a bit like Knit, but it acts only on tuple-ranges and with auto-flattening of the tuples).
Tuple-returning ranges are knit, tmap, tfilter, segment, delay, ...
and obviously any map-like range with a tuple-returning function: map, comprehension, parallelComprehension, ...
Examples:
----
auto r1 = [0,1,2,3,4,5];
auto r2 = [0.1, 0.2, 0.3, 0.4];
auto r3 = ["abc", "def", "", "g"];
auto r4 = ["a", "b", "c", "d", "e", "f"];

auto k1 = knit(r1,r2); // returns Tuple!(int, double)
auto k2 = knit(r3,r4); // returns Tuple!(string, char)
auto tf = tfilter!"b<2"(r3,r1); // returns Tuple!(string, int);

auto s = stitch(k1,k2,tf); // returns Tuple!(int,double,string,char,string,int)

assert(s.front == tuple(0, 0.1, "abc", "a", "abc", 0));
s.popFront;
assert(s.front == tuple(1, 0.2, "def", "b", "def", 1));
s.popFront;
assert(s.empty); // tf stops there because now r1's elements are not less than 2. So s stops there also.
----
*/
StitchType!R stitch(R...)(R ranges) if (allSatisfy!(isTupleRange, R))
{
    // fun is "tuple(a.expand, b.expand, c.expand)", for example for 3 ranges.
    enum string fun = "tuple(" ~ Loop!(0, R.length, Stitcher); // Loop is found in dranges.functional.d
    return tmap!fun(ranges);
}

string Stitcher(uint n, uint max) { return az(n) ~ ".expand"~ (n < max-1 ? ", " : ")");}

template StitchType(R...) if (allSatisfy!(isTupleRange, R))
{
    alias TMapType!("tuple(" ~ Loop!(0, R.length, Stitcher), R) StitchType;
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4,5];
    auto r2 = [0.1, 0.2, 0.3, 0.4];
    auto r3 = ["abc", "def", "", "g"];
    auto r4 = ["a", "b", "c", "d", "e", "f"];

    auto k1 = knit(r1, r2); // returns Tuple!(int, double)
    auto k2 = knit(r3,r4);  // returns Tuple!(string, char)
    auto tf = tfilter!"b<2"(r3,r1); // returns Tuple!(string, int);

    auto s = stitch(k1,k2,tf); // returns Tuple!(int,double,string,char,string,int)

    assert(s.front == tuple(0, 0.1, "abc", "a", "abc", 0));
    s.popFront;
    assert(s.front == tuple(1, 0.2, "def", "b", "def", 1));
    s.popFront;
    assert(s.empty); // tf stops there because now r1's elements are not less than 2. So s stops there also.
}

/**
Takes a tuple-producing range and rotate each tuple by n positions. If n>0,
it rotates to the left: takes the first n fields and put them at the end.
If n<0 it rotates to the right: takes the last n fields and put them at the beginning.

Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = [3.14, 2.78, 1.414];
auto s = ["a","b","c","d","e","f"];

// Let's create a tuple-returning range.
auto k = knit(r1,r2,s);
assert(is(ElementType!(typeof(k)) == Tuple!(int,double,string)));
assert(equal(k, [tuple(0,3.14,"a"), tuple(1,2.78,"b"), tuple(2,1.414,"c")][]));

auto rot1 = twist!1(k);
assert(is(ElementType!(typeof(rot1)) == Tuple!(double,string,int)));
assert(equal(rot1, [tuple(3.14,"a",0), tuple(2.78,"b",1), tuple(1.414,"c",2)][]));

auto rot_1 = twist!(-1)(k);
assert(is(ElementType!(typeof(rot_1)) == Tuple!(string,int,double)));
assert(equal(rot_1, [tuple("a",0,3.14), tuple("b",1,2.78), tuple("c",2,1.414)][]));
----
*/
auto twist(int n, R)(R range) if (isTupleRange!R)
{
    return map!(rotateTuple!(n,ElementType!R.Types))(range);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4];
    auto r2 = [3.14, 2.78, 1.414];
    auto s = ["a","b","c","d","e","f"];

    auto k = knit(r1,r2,s);
    assert(is(ElementType!(typeof(k)) == Tuple!(int,double,string)));
    assert(equal(k, [tuple(0,3.14,"a"), tuple(1,2.78,"b"), tuple(2,1.414,"c")][]));

    auto rot1 = twist!1(k);
    assert(is(ElementType!(typeof(rot1)) == Tuple!(double,string,int)));
    assert(equal(rot1, [tuple(3.14,"a",0), tuple(2.78,"b",1), tuple(1.414,"c",2)][]));

    auto rot_1 = twist!(-1)(k);
    assert(is(ElementType!(typeof(rot_1)) == Tuple!(string,int,double)));
    assert(equal(rot_1, [tuple("a",0,3.14), tuple("b",1,2.78), tuple("c",2,1.414)][]));
}

/**
Takes a tuple-producing range and reverse each tuple: the first field
becomes the last one, and so on.

Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = [3.14, 2.78, 1.414];
auto s = ["a","b","c","d","e","f"];

auto k = knit(r1,r2,s);
assert(is(ElementType!(typeof(k)) == Tuple!(int,double,string)));
assert(equal(k, [tuple(0,3.14,"a"), tuple(1,2.78,"b"), tuple(2,1.414,"c")][]));

auto rev = twist(k);
assert(is(ElementType!(typeof(rev)) == Tuple!(string,double,int)));
assert(equal(rev, [tuple("a",3.14,0), tuple("b",2.78,1), tuple("c",1.414,2)][]));
----
*/
auto twist(R)(R range) if (isTupleRange!R)
{
    return map!(reverseTuple!(ElementType!R.Types))(range);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4];
    auto r2 = [3.14, 2.78, 1.414];
    auto s = ["a","b","c","d","e","f"];

    auto k = knit(r1,r2,s);
    assert(is(ElementType!(typeof(k)) == Tuple!(int,double,string)));
    assert(equal(k, [tuple(0,3.14,"a"), tuple(1,2.78,"b"), tuple(2,1.414,"c")][]));

    auto rev = twist(k);
    assert(is(ElementType!(typeof(rev)) == Tuple!(string,double,int)));
    assert(equal(rev, [tuple("a",3.14,0), tuple("b",2.78,1), tuple("c",1.414,2)][]));
}

/**
Takes a tuple-producing range, range1, and another range, range2 and creates a new tuple-returning range
which inserts the elements of range2 at position n into range1's elements. As for an array, index 0
is before all other elements, etc.

Example:
----
auto r1 = [0,1,2,3,4];
auto s = ["a","b","c","d","e","f"];
auto k = knit(r1,s); // k returns Tuple!(int,string)

auto r2 = [-2.1, 0.0, 3.14];

auto spl = splice!1(k,r2); // splices r2 in the middle of k's elements.
assert(is(ElementType!(typeof(spl)) == Tuple!(int,double,string)));
assert(equal(spl, [tuple(0,-2.1,"a"), tuple(1,0.0,"b"), tuple(2, 3.14, "c")][]));

auto spl2 = splice!0(spl,k); // splices k before all spl's elements.
assert(is(ElementType!(typeof(spl2)) == Tuple!(Tuple!(int,string), int,double,string))); // non-flattening
assert(equal(spl2, [tuple(tuple(0,"a"), 0,-2.1,"a"), tuple(tuple(1,"b"),1,0.0,"b"), tuple(tuple(2,"c"),2, 3.14, "c")][]));
----

As std.typecons.Tuple is not auto-flattening, you can splice tuple-producing ranges into one another.
Example:
----
auto spl2 = splice!0(spl,k); // splices k before all spl's elements.
assert(is(ElementType!(typeof(spl2)) == Tuple!(Tuple!(int,char), int,double,char))); // non-flattening
assert(equal(spl2, [tuple(tuple(0,"a"), 0,-2.1,"a"), tuple(tuple(1,"b"),1,0.0,"b"), tuple(tuple(2,"c"),2, 3.14, "c")][]));
----
*/
auto splice(size_t n, R1, R2)(R1 range1, R2 range2)
if (allSatisfy!(isForwardRange, R1, R2) && is(ElementType!R1.Types) && (n <= ElementType!R1.Types.length)) {
    enum string splicer = "insertAtTuple!" ~ to!string(n) ~ "(a,b)";
    return tmap!splicer(range1,range2);
}

template SpliceType(size_t n, R1, R2)
{
    //alias TMapType!("insertAtTuple!" ~ to!string(n) ~ "(a,b)", R1, R2) SpliceType;
    alias typeof(splice!n(R1.init, R2.init)) SpliceType;
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4];
    auto s = ["a","b","c","d","e","f"];
    auto k = knit(r1,s);

    auto r2 = [-2.1, 0.0, 3.14];

    auto spl = splice!1(k,r2); // splices r2 in the middle of k's elements.
    assert(is(ElementType!(typeof(spl)) == Tuple!(int,double,string)));
    assert(equal(spl, [tuple(0,-2.1,"a"), tuple(1,0.0,"b"), tuple(2, 3.14, "c")][]));

    auto spl2 = splice!0(spl,k); // splices k before all spl's elements.
    assert(is(ElementType!(typeof(spl2)) == Tuple!(Tuple!(int,string), int,double,string))); // non-flattening
    assert(equal(spl2, [tuple(tuple(0,"a"), 0,-2.1,"a"), tuple(tuple(1,"b"),1,0.0,"b"), tuple(tuple(2,"c"),2, 3.14, "c")][]));
}

/**
Takes a tuple-producing range and an array of indices ([0,1,2] for example, meaning "first, second and third fields")
and returns a tuple-producing range whose elements" fields are those indicated by array.
The indices can be repeated, omitted, put in any order and the array can be longer than the input tuple ([0,1,2,3,2,1,3,1,0]).
Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = [3.14, 2.78,1.414];
string s = "abcdef";

auto k = knit(r1,r2,s);

auto shr1 = shred!([1,0])(k); // inverting the order
assert(equal(shr1, [tuple(3.14,0), tuple(2.78,1), tuple(1.414,2)][]));

auto shr2 = shred!([1])(k); // taking only one field
assert(equal(shr2, [tuple(3.14), tuple(2.78), tuple(1.414)][]));

auto shr3 = shred!([2,0,1,1])(k); // repating some fields
assert(equal(shr3, [tuple("a",0,3.14,3.14), tuple("b",1,2.78,2.78), tuple("c",2,1.414,1.414)][]));

auto shr4 = shred!([1,2,0])(shr3); // re-inverting the fields
assert(equal(shr4, k)); // this re-creates k
----
*/
/*
ShredType!(array, R) shred(alias array, R)(R range)
if (isTupleRange!R && hasLength!(typeof(array)))
{
    return map!(naryFun!(shredTuple!(array, ElementType!R.Types)))(range);
}*/

/**
Another version of shred that takes only one index. It extracts the corresponding field
from a tuple-producing range's elements and returns that as a range, 'un-tuplified'.
That is, where shred!([1])(k) will produce a tuple-returning range (one-element tuples,
but tuples nonetheless), shred!1(k) will produce a standard range.
Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = [3.14, 2.78,1.414];
auto s = ["a","b","c","d","e","f"];

auto k = knit(r1,r2,s);

auto shr1 = shred!([1,0])(k); // inverting the order
assert(equal(shr1, [tuple(3.14,0), tuple(2.78,1), tuple(1.414,2)][]));

auto shr2 = shred!([1])(k); // taking only one field
assert(equal(shr2, [tuple(3.14), tuple(2.78), tuple(1.414)][]));

auto shr3 = shred!([2,0,1,1])(k); // repating some fields
assert(equal(shr3, [tuple("a",0,3.14,3.14), tuple("b",1,2.78,2.78), tuple("c",2,1.414,1.414)][]));

auto shr4 = shred!([1,2,0])(shr3); // re-inverting the fields
assert(equal(shr4, k)); // this re-creates k

auto shr5 = shred!1(k);
assert(equal(shr5, r2));
----
*/
/*
ShredType!(n,R) shred(size_t n, R)(R range) if (isTupleRange!R)
{
    enum string shredder = "a.field[" ~ to!string(n) ~ "]";
    return map!(naryFun!shredder)(range);
}

template ShredType(alias array, R) if (isTupleRange!R && hasLength!(typeof(array)))
{
    alias Map!(naryFun!(shredTuple!(array, ElementType!R.Types)), R) ShredType;
}

template ShredType(size_t n, R) if (isTupleRange!R)
{
    alias Map!(naryFun!("a.field[" ~ to!string(n) ~ "]"), R) ShredType;
}
*/

template shred(idx...){
    static if(idx.length == 1){
        auto shred(R)(R range)
        if(isTupleRange!R)
        {
            enum pred = "a.field[" ~ idx[0].stringof ~ "]";
            return map!pred(range);
        }
    }else{
        string CreateIndex(){
            string dst = "tuple(";
            foreach(e; idx)
                dst ~= "a.field[" ~ e.stringof ~ "],";
            return dst[0..$-1] ~ ")";
        }
        
        auto shred(R)(R range)
        if(isTupleRange!R)
        {
            return map!(CreateIndex())(range);
        }
    }
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4];
    auto r2 = [3.14, 2.78,1.414];
    auto s = ["a","b","c","d","e","f"];

    auto k = knit(r1,r2,s);

    auto shr1 = shred!(1,0)(k); // inverting the order
    assert(equal(shr1, [tuple(3.14,0), tuple(2.78,1), tuple(1.414,2)][]));

    auto shr2 = shred!(1)(k); // taking only one field
    assert(equal(shr2, [3.14, 2.78, 1.414][]));

    auto shr3 = shred!(2,0,1,1)(k); // repating some fields
    assert(equal(shr3, [tuple("a",0,3.14,3.14), tuple("b",1,2.78,2.78), tuple("c",2,1.414,1.414)][]));

    auto shr4 = shred!(1,2,0)(shr3); // re-inverting the fields
    assert(equal(shr4, k)); // this re-creates k

    auto shr5 = shred!1(k);
    assert(equal(shr5, r2));
}

/**
Takes a tuple-producing range whose elements are 1-element tuples (mainly, this can happen as the result
of some extracting, shredding, filtering, etc.) and "untuplify" it, extracting the tuples values.
Example:
----
auto r1 = [0,1,2,3,4];

auto k = knit(r1);
assert(equal(k, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4)]));
auto u = untuple(k);
assert(equal(u, r1)); // u is [0,1,2,3,4]
----
See_Also: shred.
*/
TMapType!("a", R) untuplify(R)(R range) if (isTupleRange!R && ElementType!R.Types.length == 1)
{
    return tmap!("a")(range);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4];

    auto k = knit(r1);
    assert(equal(k, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4)][]));
    auto u = untuplify(k);
    assert(equal(u, r1));
}


/**
A range that iterates alternatively on the ranges given at creation. It's related
to std.range.Transversal, but will iterated on all "columns" and will stop
as soon as one of them is empty.
Example:
----
auto r1 = [0,1,2,3,4];
auto r2 = repeat(5);
auto r3 = [-2.0, -1.0, 0.0, 1.0];

auto t = transverse(r1, r2, r3);
assert(is(ElementType!(typeof(t)) == double)); // double is the common type for (int, int, double)
assert(equal(t, [0.0,5,-2,1,5,-1,2,5,0,3,5,1,4,5][])); // after 4,5, (the internal copy of) r3 is exhausted.

auto t2 = transverse(r1, emptyRange!double, emptyRange!short);
assert(is(ElementType!(typeof(t2)) == double));
assert(equal(t2, [0][])); // 0, then stops because it reaches emptyRange!double
----
*/
struct Transverse(R...) if (allSatisfy!(isForwardRange,R) && CompatibleRanges!R) {
    R _ranges;
    alias CommonElementType!R  ET;
    ET[] globalFront;
    bool willBeEmpty;

    this(R ranges) {
        _ranges = ranges;
        willBeEmpty = false;
        calculateFront;
    }

    private void calculateFront() {
        foreach(elem; _ranges) {
            if (!elem.empty) {
                globalFront ~= elem.front;
            }
            else {
                willBeEmpty = true;
                break;
            }
        }
    }

    @property bool empty() {
        return willBeEmpty && globalFront.empty;
    }

    @property Transverse save() { return this;}

    void popFront() {
        globalFront.popFront;
        if (globalFront.empty && !willBeEmpty) {
            foreach(i, elem; _ranges) _ranges[i].popFront;
            calculateFront;
        }
    }

    @property ET front() {
        return globalFront.front;
    }
}

/// ditto
Transverse!R transverse(R...)(R ranges) {
    return Transverse!(R)(ranges);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4];
    auto r2 = repeat(5);
    auto r3 = [-2.0, -1.0, 0.0, 1.0];

    auto t = transverse(r1, r2, r3);
    assert(is(ElementType!(typeof(t)) == double)); // double is the common type for (int, int, double)
    assert(equal(t, [0.0,5,-2,1,5,-1,2,5,0,3,5,1,4,5][])); // after 4,5, (the internal copy of) r3 is exhausted.

    double[] e1;
    short[] e2;
    auto t2 = transverse(r1, e1, e2);
    assert(is(ElementType!(typeof(t2)) == double));
    assert(equal(t2, [0][])); // 0, then stops because it reaches emptyRange!double
}

/**
Simple use of transverse.
Alternates between bigRange and smallRange, rolling smallRange into a cycle.
Example:
----
auto i1 = interleave("abcdef", ",");    // -> a,b,c,d,e,f,
auto i2 = interleave("abcdef", ",;.");  // -> a,b;c.d,e;f.
auto r1 = [0,1,2,3,4];
auto i3 = interleave(r1,r1);
assert(equal(i3, [0,0,1,1,2,2,3,3,4,4][]));
----
*/
Transverse!(B,Cycle!S) interleave(B, S)(B bigRange, S smallRange) {
    return transverse(bigRange, cycle(smallRange));
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto i = interleave("abcdef", ",");
    assert(asString(i) == "a,b,c,d,e,f,"); // Yes, there is a "," at the end.
    auto i2 = interleave("abcdef", ",;.");
    assert(asString(i2) == "a,b;c.d,e;f.");
    auto r1 = [0,1,2,3,4];
    auto i3 = interleave(r1,r1);
    assert(equal(i3, [0,0,1,1,2,2,3,3,4,4][]));
}

/*
template MaxArray(alias array, alias theMax = 0) {
    static if (array.length > 0) {
        alias MaxArray!(array[1..$], max(theMax, array[0])) MaxArray;
    }
    else {
        alias theMax MaxArray;
    }
}*/
/*
template MaxArray(alias array, int theMax = 0)if(isArray(typeof(array)) && array.length != 0){
    static if(array.length == 1)
        enum MaxArray = max(theMax, array[0]);
    else
        enum MaxArray = MaxArray!(array[1..$], max(theMax, array[0]));
}*/

/**
Generate range whose elements were cutted a range into segments of n-length.

If the original range is a bidirectional-range, segment is one.
Also, forward-range, random-access-range, infinite-range and a range which has assignable-elements.
But, if the original range has swappable-elements or lvalue-elements, the generated range has assignable-elements.
And, if the original range is input-range and has assignable-elements, the generated range doesn't have assignable-elements.

See_Also: delay, parallel.

when the original range is a array,
it is true that type judging (isRandomAccessRange!(Unqual!Range) && isBidirectionalRange!(Unqual!Range) && hasLength!(Unqual!Range)).
Examples:
----
auto r1 = [0, 1, 2, 3, 4, 5];
auto s = segment!2(r1);
assert(equal(s, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4), tuple(4, 5)][]));
assert(s.length == 5);         // .length
// back/popBack:
assert(equal(retro(s), retro([tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4), tuple(4, 5)][])));
assert(s[3] == tuple(3, 4));    // opIndex
s[3] = tuple(0, 0);             // opIndexAssign not ref opIndex
assert(s[2] == tuple(2, 0));    // it affects its neighbors.
assert(s[4] == tuple(0, 5));
assert(r1 == [0, 1, 2, 0, 0, 5][]); // affects r1 back (no .dup internally)


auto st = ["a","b","c","d","e","f"];
auto s2 = segment!3(st);
assert(s2.front == tuple("a","b","c"));


auto r1 = [0,1,2,3,4,5]; // regenerates r1
auto s3 = segment!1(r1);
assert(equal(s3, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4), tuple(5)][]));
auto r2 = map!"a*a"(r1);
auto s4 = segment!2(r2); // On a forward range
assert(equal(s4, [tuple(0,1), tuple(1,4), tuple(4,9), tuple(9,16), tuple(16,25)][]));


int[] e;
auto s5 = segment!2(e);
assert(s5.empty);
----

Authors: Komatsu Kazuki
*/
template SegmentType(size_t N, R)
if(isInputRange!(Unqual!R) && N > 0)
{
    alias typeof(segment!N(R.init)) SegmentType;
}


///ditto
template segment(size_t N : 1, Range)
if(isInputRange!(Unqual!Range))
{
    Segment segment(Range range)
    {
        return Segment(range);
    }

    alias Unqual!Range R;
    alias ElementType!Range E;

    struct Segment{
    private:
        R _range;

    public:
        this(R range)
        {
            _range = range;
        }


      static if(isInfinite!R)
        enum bool e = false;
      else
        @property bool empty()
        {
            return _range.empty;
        }
        
        
        void popFront()
        {
            _range.popFront();
        }
      static if(isBidirectionalRange!R)
        void popBack()
        {
            _range.popBack();
        }
        
        
      static if(isForwardRange!R)
        @property typeof(this) save()
        {
            typeof(this) dst = this;
            dst._range = dst._range.save;
            return dst;
        }
      
      static if(hasLength!R)
      {
        @property size_t length()
        {
            return _range.length;
        }

        alias length opDollar;
      }
      
      static if(hasSlicing!R)
      {
        Segment opSlice()
        {
          static if(isForwardRange!R)
            return save;
          else
            return typeof(this)(_range);
        }


        auto opSlice(size_t i, size_t j)
        {
            return segment!1(_range[i .. j]);
        }
      }
      
      
        @property Tuple!E front()
        {
            return tuple(_range.front);
        }
        
      static if(isBidirectionalRange!R)
        @property Tuple!E back()
        {
            return tuple(_range.back);
        }
      
      static if(isRandomAccessRange!R)
        Tuple!E opIndex(size_t i)
        {
            return tuple(_range[i]);
        }

      static if(hasAssignableElements!R || hasSwappableElements!R || hasLvalueElements!R)
      {
        @property void front(Tuple!E e)
        {
            _range.front = e[0];
        }

        
        static if(isBidirectionalRange!R)
        {
          @property void back(Tuple!E e)
          {
              _range.back = e[0];
          }
        }
        
        static if(isRandomAccessRange!R)
        {
          void opIndexAssign(Tuple!E e, size_t i)
          {
              _range[i] = e[0];
          }
        }
      }
    
    }
}


unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto a = [0, 1, 2, 3, 4];
    auto sg = segment!1(a);

    assert(equal(sg, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4)]));
    assert(equal(sg.retro, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4)].retro));

    sg.front = tuple(3);
    assert(equal(sg, [tuple(3), tuple(1), tuple(2), tuple(3), tuple(4)]));

    sg[3] = tuple(2);
    assert(equal(sg, [tuple(3), tuple(1), tuple(2), tuple(2), tuple(4)]));

    assert(sg.length == 5);

    sg.back = tuple(8);
    assert(equal(sg, [tuple(3), tuple(1), tuple(2), tuple(2), tuple(8)]));
    assert(sg[$-1] == tuple(8));

    assert(equal(sg[2..4], [tuple(2), tuple(2)]));

    auto sv = sg.save;
    sv.popFront();
    assert(equal(sg, [tuple(3), tuple(1), tuple(2), tuple(2), tuple(8)]));
    assert(equal(sv, [tuple(1), tuple(2), tuple(2), tuple(8)]));

    auto sl = sv[];
    sv.popFront();
    assert(equal(sl, [tuple(1), tuple(2), tuple(2), tuple(8)]));
    assert(equal(sv, [tuple(2), tuple(2), tuple(8)]));
}


///ditto
template segment(size_t N, Range)
if (isInputRange!(Unqual!Range) 
&& (isForwardRange!(Unqual!Range) ? (!isBidirectionalRange!(Unqual!Range)
                                      && !isRandomAccessRange!(Unqual!Range)) : true))
{
    Segment segment(Range range)
    {
        return Segment(range);
    }

    alias Unqual!Range R;
    alias ElementType!R E;

    enum assE = isForwardRange!R && (hasAssignableElements!R || hasLvalueElements!R || hasSwappableElements!R);

    struct Segment{
    private:
        R _range;
        E[] _front;

      static if(assE)
        R _assignRange;

    public:
        this(R range)
        {
            _range = range;

          static if(assE)
            _assignRange = _range.save;

            for(int i = 0; i < N && !_range.empty; ++i, _range.popFront())
                _front ~= _range.front;
        }


        void popFront()
        {
            if(_range.empty)
                _front = _front[1..$];
            else{
                _front = _front[1..$];
                _front ~= _range.front;
                _range.popFront();
              static if(assE)
                _assignRange.popFront();
            }
        }

        @property
        Tuple!(TypeNuple!(E, N)) front()
        {
            return (cast(typeof(return)[])(cast(ubyte[])_front))[0];
        }


      static if(assE)
        @property void front(Tuple!(TypeNuple!(E, N)) e)
        {
            R _tmpRange = _assignRange.save;

            _front = [e.field];

            for(int i = 0; i < N; ++i, _tmpRange.popFront)
                _tmpRange.front = _front[i];
        }


      static if(isForwardRange!R) {
        @property Segment save()
        {
            Segment dst = this;
            dst._range = dst._range.save;

          static if(assE)
            dst._assignRange = dst._assignRange.save;

            return dst;
        }
      }

      static if(isInfinite!R)
        enum bool empty = false;        
      else
        @property
        bool empty()
        {
            return _front.length != N;
        }
        

      static if(hasLength!R){
        @property
        size_t length()
        {
          return _range.length + !this.empty;
        }

        alias length opDollar;
      }

      static if(hasSlicing!R)
      {
          Segment opSlice()
          {
            static if(isInputRange!R)
              return this;
            else
              return save;
          }

          auto opSlice(size_t i, size_t j)
          {
              return segment!N(_assignRange[i..j + (N-1)]);
          }
      }
    }
}


unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    struct TRange
    {
        int _front, _end;
        @property int front(){return _front;}
        void popFront(){_front += 1;}
        @property bool empty(){return _front == _end;}
        @property TRange save(){return this;}
        @property size_t length(){return _end - _front;}
        alias length opDollar;
    }

    auto tr = TRange(0, 5);
    auto sg2 = segment!2(tr);
    assert(equal(sg2, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)]));

    auto sg2sv = sg2.save;
    sg2sv.popFront();
    assert(equal(sg2, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)]));
    assert(equal(sg2sv, [tuple(1, 2), tuple(2, 3), tuple(3, 4)]));

    assert(sg2.length == 4);

    auto sg3 = segment!3(tr);
    assert(equal(sg3, [tuple(0, 1, 2), tuple(1, 2, 3), tuple(2, 3, 4)]));
    assert(sg3.length == 3);

    auto sg4 = segment!4(tr);
    assert(equal(sg4, [tuple(0, 1, 2, 3), tuple(1, 2, 3, 4)]));
    assert(sg4.length == 2);

    auto sg5 = segment!5(tr);
    assert(equal(sg5, [tuple(0, 1, 2, 3, 4)]));
    assert(sg5.length == 1);

    auto sg6 = segment!6(tr);
    assert(sg6.empty);
    assert(sg6.length == 0);

    auto tremp = TRange(0, 0);
    assert(tremp.empty);
    assert(segment!2(tremp).empty);
}
unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    struct TRange
    {
        int _front, _end;
        @property int front(){return _front;}
        void popFront(){_front += 1;}
        @property bool empty(){return _front == _end;}
        @property TRange save(){return this;}
        @property size_t length(){return _end - _front;}
        alias length opDollar;
    }

    auto tr = TRange(0, 5);
    auto sg2 = segment!2(tr);
    assert(equal(sg2, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)]));

    assert(sg2.length == 4);

    auto sg3 = segment!3(tr);
    assert(equal(sg3, [tuple(0, 1, 2), tuple(1, 2, 3), tuple(2, 3, 4)]));
    assert(sg3.length == 3);

    auto sg4 = segment!4(tr);
    assert(equal(sg4, [tuple(0, 1, 2, 3), tuple(1, 2, 3, 4)]));
    assert(sg4.length == 2);

    auto sg5 = segment!5(tr);
    assert(equal(sg5, [tuple(0, 1, 2, 3, 4)]));
    assert(sg5.length == 1);

    auto sg6 = segment!6(tr);
    assert(sg6.empty);
    assert(sg6.length == 0);

    auto tremp = TRange(0, 0);
    assert(tremp.empty);
    assert(segment!2(tremp).empty);
}
unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    struct TRange
    {
        int[] a;
        @property ref int front(){return a.front;}
        @property bool empty(){return a.empty;}
        void popFront(){a.popFront;}
        @property TRange save(){return TRange(a.save);}
        @property size_t length(){return a.length;}
        alias length opDollar;
        TRange opSlice(size_t i, size_t j){return TRange(a[i..j]);}
    }


    int[] a = [0, 1, 2, 3, 4];
    auto r = TRange(a);
    auto sg = segment!2(r);
    assert(equal(sg, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)]));
    assert(equal(sg[2..4], [tuple(2, 3), tuple(3, 4)]));

    sg.front = tuple(3, 2);
    assert(equal(sg, [tuple(3, 2), tuple(2, 2), tuple(2, 3), tuple(3, 4)]));

    assert(sg.length == 4);
    sg.popFront();
    assert(sg.length == 3);
    sg.popFront();
    assert(sg.length == 2);
    sg.popFront();
    assert(sg.length == 1);
    sg.popFront();
    assert(sg.length == 0);
    assert(sg.empty);

    a = [0, 1, 2, 3, 4];
    r = TRange(a);
    auto sg3 = segment!3(r);
    assert(equal(sg3, [tuple(0, 1, 2), tuple(1, 2, 3), tuple(2, 3, 4)]));
    sg3.front = tuple(2, 3, 1);
    assert(equal(sg3, [tuple(2, 3, 1), tuple(3, 1, 3), tuple(1, 3, 4)]));

    auto sl3 = sg3[];
    sl3.popFront();
    assert(equal(sg3, [tuple(2, 3, 1), tuple(3, 1, 3), tuple(1, 3, 4)]));
    assert(equal(sl3, [tuple(3, 1, 3), tuple(1, 3, 4)]));

    auto sv3 = sg3.save;
    sv3.popFront();
    assert(equal(sg3, [tuple(2, 3, 1), tuple(3, 1, 3), tuple(1, 3, 4)]));
    assert(equal(sv3, [tuple(3, 1, 3), tuple(1, 3, 4)]));

    assert(sg3.length == 3);
    sg3.popFront();
    assert(sg3.length == 2);
    sg3.popFront();
    assert(sg3.length == 1);
    sg3.popFront();
    assert(sg3.length == 0);
    assert(sg3.empty);
}


///ditto
template segment(size_t N, Range)
if(isRandomAccessRange!(Unqual!Range)
&& isBidirectionalRange!(Unqual!Range)
&& hasLength!(Unqual!Range))
{
    Segment segment(Range range)
    {
        return Segment(range);
    }


    alias Unqual!Range R;
    alias ElementType!R E;
    
    struct Segment{
      private:
        R _range;
        size_t _fidx;
        size_t _bidx;
        E[] _front;
        E[] _back;

        void reConstruct()
        {
            if(!empty){
                _front.length = 0;
                _back.length = 0;
                foreach(i; 0..N)
                {
                    _front ~= _range[_fidx + i];
                    _back ~= _range[_bidx + i];
                }
            }
        }


      public:
        this(R range)
        {
            _range = range;
            _fidx = 0;
            _bidx = _range.length - N;

            reConstruct();
        }

        
        @property bool empty() const
        {
            return (cast(int)_bidx - cast(int)_fidx) < 0;
        }

        
        void popFront()
        {
            ++_fidx;
            if(!empty){
                _front = _front[1..$];
                _front ~= _range[_fidx + (N - 1)];
            }
        }


        void popBack()
        {
            --_bidx;
            if(!empty){
                _back = _back[0..$-1];
                _back = [_range[_bidx]] ~ _back;
            }
        }
        
        
        @property Segment save()
        {
            Segment dst = cast(Segment)this;
            dst._range = dst._range.save;
            dst._front = dst._front.dup;
            dst._back = dst._back.dup;
            return dst;
        }
      

        @property size_t length() const
        {
            return _bidx - _fidx + 1;
        }


        alias length opDollar;
      

        auto opSlice()
        {
            return save;
        }


        Segment opSlice(size_t i, size_t j)
        {
            Segment dst = this.save;
            dst._fidx += i;
            dst._bidx -= this.length - j;

            dst.reConstruct();
            return dst;
        }
      

        @property Tuple!(TypeNuple!(E, N)) front()
        {
            return (cast(typeof(return)[])(cast(ubyte[])_front))[0];
        }


        @property Tuple!(TypeNuple!(E, N)) back()
        {
            return (cast(typeof(return)[])(cast(ubyte[])_back))[0];
        }


        Tuple!(TypeNuple!(E, N)) opIndex(size_t i)
        {
            if(i == 0)
                return this.front;
            else if(i == this.length - 1)
                return this.back;
            else
            {
                E[] dst;
                foreach(j; 0 .. N)
                    dst ~= _range[_fidx + i + j];
                return (cast(typeof(return)[])(cast(ubyte[])dst))[0];
            }
        }


      static if(hasSwappableElements!R || hasLvalueElements!R || hasAssignableElements!R)
      {
        @property void front(Tuple!(TypeNuple!(E, N)) e)
        {
            E[] eSlice = [e.field];

            foreach(i; 0 .. N)
                _range[i + _fidx] = eSlice[i];
            
            reConstruct();
        }


        @property void back(Tuple!(TypeNuple!(E, N)) e)
        {
            E[] eSlice = [e.field];

            foreach(i; 0..N)
                _range[i + _bidx] = eSlice[i];

            reConstruct();
        }


        void opIndexAssign(Tuple!(TypeNuple!(E, N)) e, size_t i)
        {
            E[] eSlice = [e.field];

            foreach(j; 0..N)
                _range[_fidx + i + j] = eSlice[j];

            reConstruct();
        }
      }
    }
}


unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4,5];
    auto s = segment!2(r1);
    assert(equal(s, [tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][]));
    assert(s.length == 5);         // .length
    // back/popBack:
    assert(equal(retro(s), retro([tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][])));
    assert(s[3] == tuple(3,4));    // opIndex
    s[3] = tuple(0,0);             // opIndexAssign
    assert(s[2] == tuple(2,0));    // it affects its neighbors.
    assert(s[4] == tuple(0,5));
    assert(r1 == [0,1,2,0,0,5][]); // affects r1 back (no .dup internally)

    s = segment!2(r1);
    s.front = tuple(2, 0);
    assert(s[0] == tuple(2, 0));

    s.back = tuple(100, 500);
    assert(s[s.length - 1] == tuple(100, 500));

    auto sl = s[];
    assert(equal(sl, s));
    sl.popFront();
    sl.popBack();
    assert(equal(sl, s[1 .. s.length - 1]));
}
unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto st = ["a","b","c","d","e","f"];
    auto s2 = segment!3(st);
    assert(s2.front == tuple("a","b","c"));
}
unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4,5]; // regenerates r1
    auto s3 = segment!1(r1);
    assert(equal(s3, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4), tuple(5)][]));
    assert(equal(s3.retro, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4), tuple(5)].retro));
    auto r2 = map!"a*a"(r1);
    auto s4 = segment!2(r2); // On a forward range
    assert(equal(s4, [tuple(0,1), tuple(1,4), tuple(4,9), tuple(9,16), tuple(16,25)][]));
}
unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    int[] e;
    auto s5 = segment!2(e);
    assert(s5.empty);
}
unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto ri = iota(0, 5);
    auto sg = segment!2(ri);
    assert(equal(sg, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)]));
    assert(equal(sg.retro, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)].retro));
    assert(sg[0] == tuple(0, 1));
    assert(sg[1] == tuple(1, 2));
    assert(sg[2] == tuple(2, 3));
    assert(sg[3] == tuple(3, 4));
    assert(sg.length == 4);
}

///ditto
template segment(size_t N, Range)
if(isRandomAccessRange!(Unqual!Range)
&& !isBidirectionalRange!(Unqual!Range)
&& isInfinite!(Unqual!Range))
{
    Segment segment(Range range)
    {
        return Segment(range);
    }


    alias Unqual!Range R;
    alias ElementType!R E;
    
    struct Segment{
      private:
        R _range;
        size_t _fidx;
        E[] _front;

        void reConstruct()
        {
            if(!empty){
                _front.length = 0;
                foreach(i; 0..N)
                    _front ~= _range[_fidx + i];
            }
        }

      public:
        this(R range)
        {
            _range = range;
            _fidx = 0;

            reConstruct();
        }

        
        enum bool empty = false;

        
        void popFront()
        {
            ++_fidx;
            if(!empty){
                _front = _front[1..$];
                _front ~= _range[_fidx + (N - 1)];
            }
        }
        
        
        @property Segment save()
        {
            Segment dst = this;
            dst._range = dst._range.save;
            return dst;
        }
      

      @property Tuple!(TypeNuple!(E, N)) front()
      {
          return (cast(typeof(return)[])(cast(ubyte[])_front))[0];
      }


      Tuple!(TypeNuple!(E, N)) opIndex(size_t i)
      {
          if(i == 0)
              return this.front;
          else
          {
              E[] dst;
              foreach(j; 0 .. N)
                  dst ~= _range[_fidx + i + j];
              return (cast(typeof(return)[])(cast(ubyte[])dst))[0];
          }
      }


      static if(hasSwappableElements!R || hasLvalueElements!R || hasAssignableElements!R)
      {
        @property void front(Tuple!(TypeNuple!(E, N)) e)
        {
            E[] eSlice = [e.field];

            foreach(i; 0 .. N)
                _range[i + _fidx] = eSlice[i];
            
            reConstruct();
        }


        void opIndexAssign(Tuple!(TypeNuple!(E, N)) e, size_t i)
        {
            E[] eSlice = [e.field];

            foreach(j; 0..N)
                _range[_fidx + i + j] = eSlice[j];

            reConstruct();
        }
      }
    }
}


unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    struct TRange
    {
        int[] a, s;

        this(int[] r){
            a = r.save;
            s = r.save;
        }

        @property ref int front(){return a.front;}
        enum bool empty = false;
        void popFront(){a.popFront; if(a.empty)a = s;}
        @property typeof(this) save(){return this;}
        ref int opIndex(size_t i){return a[i%s.length];}
    }

    
    auto r = segment!2(TRange([0, 1, 2, 3, 4]));
    assert(equal(r.take(4), [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)]));

    auto sv = r.save;
    sv.popFront();
    assert(equal(r.take(4), [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)]));
    assert(equal(sv.take(3), [tuple(1, 2), tuple(2, 3), tuple(3, 4)]));

    assert(r[2] == tuple(2, 3));
    assert(r[0] == tuple(0, 1));

    r.front = tuple(100, 50);
    assert(equal(r.take(4), [tuple(100, 50), tuple(50, 2), tuple(2, 3), tuple(3, 4)]));

    r[1] = tuple(10, 20);
    assert(equal(r.take(4), [tuple(100, 10), tuple(10, 20), tuple(20, 3), tuple(3, 4)]));
}


///ditto
template segment(size_t N, Range)
if(isBidirectionalRange!(Unqual!Range)
&& (isRandomAccessRange!(Unqual!Range) ? (!hasLength!(Unqual!Range) && isInfinite!(Unqual!Range)) : true))
{
    Segment segment(Range range)
    {
        return Segment(range);
    }


    alias Unqual!Range R;
    alias ElementType!R E;
    enum assE = hasAssignableElements!R && hasLvalueElements!R && hasSwappableElements!R;


    struct Segment{
      private:
        R _fRange;
        R _bRange;
        E[] _front;
        E[] _back;

      static if(assE || isRandomAccessRange!R)
        R _assignRange;

      static if(assE || isRandomAccessRange!R)
        void reConstruct(){
            _front.length = 0;
            _back.length = 0;

            _fRange = _assignRange.save;
            _bRange = _assignRange.save;

            for(int i = 0; i < N && !_fRange.empty; ++i, _fRange.popFront())
                _front ~= _fRange.front();

            for(int i = 0; i < N && !_bRange.empty; ++i, _bRange.popBack())
                _back ~= _bRange.back();

            _back.reverse();
        }



      public:
        this(R range)
        {
            _fRange = range.save;
            _bRange = range.save;

          static if(assE || isRandomAccessRange!R)
            _assignRange = range.save;

            for(int i = 0; i < N && !_fRange.empty; ++i, _fRange.popFront())
                _front ~= _fRange.front();

            for(int i = 0; i < N && !_bRange.empty; ++i, _bRange.popBack())
                _back ~= _bRange.back();

            _back.reverse();
        }

        
      static if(isInfinite!R)
        enum bool empty = false;
      else
        @property bool empty()
        {
            return (_front.length < N) || (_back.length < N);
        }
        
        
        void popFront()
        {
            _front = _front[1..$];

            if(!_fRange.empty){
              _front ~= _fRange.front;

              _fRange.popFront();
              _bRange.popFront();
            }

          static if(assE || isRandomAccessRange!R)
            _assignRange.popFront();
        }


        void popBack()
        {
            _back = _back[0..$-1];

            if(!_bRange.empty){
              _back = [_bRange.back] ~ _back;

              _fRange.popBack();
              _bRange.popBack();
            }

          static if(assE || isRandomAccessRange!R)
            _assignRange.popBack();
        }
        
        
        @property Segment save()
        {
            Segment dst = this;
            dst._fRange = dst._fRange.save;
            dst._bRange = dst._bRange.save;

          static if(assE)
            dst._assignRange = dst._assignRange.save;

            return dst;
        }

      
      static if(hasLength!R)
      {
        @property size_t length()
        {
            return _fRange.length + ((_front.length == N && _back.length == N) ? 1 : 0);
        }


        alias length opDollar;
      }
      

      static if(hasSlicing!R)
      {
        Segment opSlice()
        {
            return save;
        }


        static if(assE || isRandomAccessRange!R)
          auto opSlice(size_t i, size_t j)
          {
              return segment!N(_assignRange[i..j + (N-1)]);
          }
        //else
      }
      

        @property Tuple!(TypeNuple!(E, N)) front()
        {
            return (cast(typeof(return)[])(cast(ubyte[])_front))[0];
        }

        
        @property Tuple!(TypeNuple!(E, N)) back()
        {
            return (cast(typeof(return)[])(cast(ubyte[])_back))[0];
        }


      static if(isRandomAccessRange!R)
        Tuple!(TypeNuple!(E, N)) opIndex(size_t i)
        {
            E[] dst;

            foreach(j; 0..N)
                dst ~= _assignRange[i + j];

            return (cast(typeof(return)[])(cast(ubyte[])dst))[0];
        }



      static if(assE)
      {
        @property void front(Tuple!(TypeNuple!(E, N)) e)
        {
            R _tmp = _assignRange.save;
            _front = [e.field];

            for(int i = 0; i < N; ++i, _tmp.popFront())
                _tmp.front = _front[i];

            reConstruct();
        }


        @property void back(Tuple!(TypeNuple!(E, N)) e)
        {
            R _tmp = _assignRange.save;
            _back = [e.field];

            for(int i = N-1; i >= 0; --i, _tmp.popBack())
                _tmp.back = _back[i];

            reConstruct();
        }

        static if(isRandomAccessRange!R)
        void opIndexAssign(Tuple!(TypeNuple!(E, N)) e, size_t i)
        {
            foreach(j; 0..N)
                _assignRange[i + j] = [e.field][j];

            reConstruct();
        }
      }
    }
}

unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    struct TRange{
        int[] a;
        @property int front(){return a.front;}
        @property bool empty(){return a.empty;}
        void popFront(){a.popFront();}
        void popBack(){a.popBack();}
        @property int back(){return a.back();}
        @property TRange save(){return TRange(a.save);}
        @property size_t length(){return a.length;}
        alias length opDollar;
    }


    auto r = TRange([0, 1, 2, 3, 4]);
    auto sg = segment!2(r);
    assert(equal(sg, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)]));
    assert(equal(sg.retro, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)].retro));
    assert(sg.length == 4);

    sg.popFront();
    assert(equal(sg, [tuple(1, 2), tuple(2, 3), tuple(3, 4)]));
    assert(sg.length == 3);
    assert(!sg.empty);

    auto sv = sg.save;
    sv.popFront();
    assert(equal(sg, [tuple(1, 2), tuple(2, 3), tuple(3, 4)]));
    assert(equal(sv, [tuple(2, 3), tuple(3, 4)]));
    assert(sg.length == 3);
    assert(sv.length == 2);
    assert(!sg.empty);
    assert(!sv.empty);

    sg.popFront();
    assert(equal(sg, [tuple(2, 3), tuple(3, 4)]));
    assert(sg.length == 2);
    assert(!sg.empty);

    sg.popFront();
    assert(equal(sg, [tuple(3, 4)]));
    assert(sg.length == 1);
    assert(!sg.empty);

    sg.popFront();
    assert(sg.length == 0);
    assert(sg.empty);
}
unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    struct TRange{
        int[] a;
        @property ref int front(){return a.front;}
        @property bool empty(){return a.empty;}
        void popFront(){a.popFront();}
        void popBack(){a.popBack();}
        @property ref int back(){return a.back();}
        @property TRange save(){return TRange(a.save);}
        @property size_t length(){return a.length;}
        TRange opSlice(size_t i, size_t j){return TRange(a[i..j]);}
        alias length opDollar;
    }


    auto r = TRange([0, 1, 2, 3, 4]);
    auto sg = segment!2(r);
    assert(equal(sg, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)]));
    assert(equal(retro(sg), [tuple(3, 4), tuple(2, 3), tuple(1, 2), tuple(0, 1)]));
    assert(sg.length == 4);
    assert(equal(sg[2..4], [tuple(2, 3), tuple(3, 4)]));

    auto sgsv = sg.save;
    sgsv.popFront();
    assert(equal(sg, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)]));
    assert(equal(sgsv, [tuple(1, 2), tuple(2, 3), tuple(3, 4)]));

    auto sgsv2 = sg[];
    sgsv2.popFront();
    assert(equal(sg, [tuple(0, 1), tuple(1, 2), tuple(2, 3), tuple(3, 4)]));
    assert(equal(sgsv2, [tuple(1, 2), tuple(2, 3), tuple(3, 4)]));


    sg.front = tuple(2, 2);
    assert(equal(sg, [tuple(2, 2), tuple(2, 2), tuple(2, 3), tuple(3, 4)]));
    assert(equal(retro(sg), [tuple(3, 4), tuple(2, 3), tuple(2, 2), tuple(2, 2)]));

    sg.popFront();
    assert(equal(sg, [tuple(2, 2), tuple(2, 3), tuple(3, 4)]));
    assert(equal(retro(sg), [tuple(3, 4), tuple(2, 3), tuple(2, 2)]));
    assert(sg.length == 3);
    assert(!sg.empty);

    sg.popFront();
    assert(equal(sg, [tuple(2, 3), tuple(3, 4)]));
    assert(equal(retro(sg), [tuple(3, 4), tuple(2, 3)]));
    assert(sg.length == 2);
    assert(!sg.empty);

    sg.popFront();
    assert(equal(sg, [tuple(3, 4)]));
    assert(equal(retro(sg), [tuple(3, 4)]));
    assert(sg.length == 1);
    assert(!sg.empty);

    sg.front = tuple(2, 5);
    assert(equal(sg, [tuple(2, 5)]));
    assert(equal(retro(sg), [tuple(2, 5)]));
    assert(sg.length == 1);
    assert(!sg.empty);

    sg.front = tuple(2, 1);
    assert(equal(sg, [tuple(2, 1)]));
    assert(sg.length == 1);
    assert(!sg.empty);

    sg.popFront();
    assert(sg.length == 0);
    assert(sg.empty);
}
unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    struct TRange{
        int[] a;
        @property ref int front(){return a.front;}
        @property bool empty(){return a.empty;}
        void popFront(){a.popFront();}
        void popBack(){a.popBack();}
        @property ref int back(){return a.back();}
        @property TRange save(){return TRange(a.save);}
        @property size_t length(){return a.length;}
        TRange opSlice(size_t i, size_t j){return TRange(a[i..j]);}
        alias length opDollar;
    }


    auto r = TRange([0, 1, 2, 3, 4]);
    auto sg = segment!3(r);
    assert(equal(sg, [tuple(0, 1, 2), tuple(1, 2, 3), tuple(2, 3, 4)]));
    assert(equal(retro(sg), [tuple(0, 1, 2), tuple(1, 2, 3), tuple(2, 3, 4)].retro));
    assert(sg.length == 3);
    assert(equal(sg[2..3], [tuple(2, 3, 4)]));

    sg.front = tuple(2, 2, 2);
    assert(equal(sg, [tuple(2, 2, 2), tuple(2, 2, 3), tuple(2, 3, 4)]));
    assert(equal(sg.retro, [tuple(2, 2, 2), tuple(2, 2, 3), tuple(2, 3, 4)].retro));

    sg.popFront();
    assert(equal(sg, [tuple(2, 2, 3), tuple(2, 3, 4)]));
    assert(equal(sg.retro, [tuple(2, 2, 3), tuple(2, 3, 4)].retro));
    assert(sg.length == 2);
    assert(!sg.empty);

    sg.back = tuple(4, 4, 4);
    assert(equal(sg, [tuple(2, 4, 4), tuple(4, 4, 4)]));
    assert(equal(sg.retro, [tuple(2, 4, 4), tuple(4, 4, 4)].retro));
    assert(sg.length == 2);
    assert(!sg.empty);

    sg.popFront();
    assert(equal(sg, [tuple(4, 4, 4)]));
    assert(equal(sg.retro, [tuple(4, 4, 4)].retro));
    assert(sg.length == 1);
    assert(!sg.empty);

    sg.popFront();
    assert(sg.length == 0);
    assert(sg.empty);
}
unittest
{
    //debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    struct TRange{
        size_t f, b;
        int[] s;

        this(int[] r){
            f = 0;
            s = r;
            b = s.length - 1;
        }

        @property ref int front(){return s[f];}
        enum bool empty = false;
        void popFront(){++f; if(f == s.length)f = 0;}
        void popBack(){b = (b == 0 ? s.length - 1 : b-1);}
        @property ref int back(){return s[b];}
        @property typeof(this) save(){return this;}
        auto opSlice(size_t i, size_t j){auto dst = this; dst.popFrontN(i); return dst.take(j - i);}
        ref int opIndex(size_t i){return s[(i+f)%s.length];}
    }

    alias TRange Range;
    static assert(isInputRange!TRange);

    auto r = TRange([0, 1, 2, 3, 4]);
    auto sg = segment!3(r);
    assert(equal(sg.take(3), [tuple(0, 1, 2), tuple(1, 2, 3), tuple(2, 3, 4)]));
    assert(equal(retro(sg).take(3), [tuple(2, 3, 4), tuple(1, 2, 3), tuple(0, 1, 2)]));
    assert(sg[2] == tuple(2, 3, 4));
    //assert(equal(sg[2..3], [tuple(2, 3, 4)]));

    sg.front = tuple(2, 2, 2); //[2, 2, 2, 3, 4]
    assert(equal(sg.take(3), [tuple(2, 2, 2), tuple(2, 2, 3), tuple(2, 3, 4)]));
    assert(equal(retro(sg).take(3), [tuple(2, 3, 4), tuple(2, 2, 3), tuple(2, 2, 2)]));

    sg.popFront();
    assert(equal(sg.take(3), [tuple(2, 2, 3), tuple(2, 3, 4), tuple(3, 4, 2)]));
    assert(equal(retro(sg).take(3), [tuple(2, 3, 4), tuple(2, 2, 3), tuple(2, 2, 2)]));
    assert(!sg.empty);

    sg[1] = tuple(3, 3, 3); //[2, 2, 3, 3, 3] 
    assert(equal(sg.take(3), [tuple(2, 3, 3), tuple(3, 3, 3), tuple(3, 3, 2)]));
    assert(equal(sg.retro.take(3), [tuple(3, 3, 3), tuple(2, 3, 3), tuple(2, 2, 3)]));
    assert(!sg.empty);

    sg.back = tuple(2, 3, 4);//[2, 2, 2, 3, 4]
    assert(equal(sg.take(3), [tuple(2, 2, 3), tuple(2, 3, 4), tuple(3, 4, 2)]));
    assert(equal(sg.retro.take(3), [tuple(2, 3, 4), tuple(2, 2, 3), tuple(2, 2, 2)]));
    assert(!sg.empty);

    sg.popBack();
    assert(equal(sg.take(3), [tuple(2, 2, 3), tuple(2, 3, 4), tuple(3, 4, 2)]));
    assert(equal(sg.retro.take(3), [tuple(2, 2, 3), tuple(2, 2, 2), tuple(4, 2, 2)]));
    assert(!sg.empty);
}



/**
A generalization of segment: given an array of indices (as template argument) and a range,
it will produce the corresponding "extracts" (disjointed segments, as tuples).
segment!n(r) is equivalent to delay!([0,1,2, ...,n])(r).

But delay is much more powerful than segment.
----
delay!([2,1,0])(r);  // You can invert the values
delay!([4,9,2,0])(r); // take them from everywhere in the range
delay!([0,0,1])(r); // repeat some values
----

See_Also: segment, parallel.
Example:
----
auto r1 = [0,1,2,3,4,5];
auto d = delay!([0,1])(r1); // will iterate on the pair ([0,1,2,3,4,5], [1,2,3,4,5]).
                            // It's equivalent to segment!2(r1)
assert(equal(d, [tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][]));
assert(d.length == 5);         // .length
// back/popBack:
assert(equal(retro(d), retro([tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][])));

auto d2 = delay!([1,0])(r1); // inverting
assert(equal(d2, [tuple(1,0), tuple(2,1), tuple(3,2), tuple(4,3), tuple(5,4)][]));

auto d3 = delay!([0])(r1);   // one element
assert(equal(d3, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4), tuple(5)][]));

auto d4 = delay!([4,1,3,2])(r1); // disjoint extracts
assert(d4.front == tuple(4,1,3,2));
assert(d4.length == 2); // d4 is [(4,1,3,2),(5,2,4,3)]

auto d5 = delay!([0,0,1])(r1); // repeated values
assert(d5.front == tuple(0,0,1));

auto d6 = delay!([9,0])(r1);
assert(d6.empty);

int[] e;
assert(delay!([0,1])(e).empty);
----
*/
/*
Knit!(TypeNuple!(R, array.length)) delay(alias array, R)(R range) if (isForwardRange!R && isArray!(typeof(array)) && array.length > 0)
{
    enum size_t l = array.length;
    TypeNuple!(R, l) _ranges;
    enum m = MaxArray!array;

    foreach(i, Unused; _ranges) {
        _ranges[i] = range;
       popFrontN( _ranges[i], array[i]);
        static if (isBidirectionalRange!R) {
            popBackN(_ranges[i], m-array[i]);
        }
    }
    return knit(_ranges);
}
*/

template delay(alias array)if(isArray!(typeof(array)) && array.length != 0){

    enum Max = reduce!max(0, array);

    template ExpandArray(alias arr){
        static if(arr.length == 0)
            static assert(0);
        else static if(arr.length == 1)
            alias TypeTuple!(arr[0]) ExpandArray;
        else
            alias TypeTuple!(arr[0], ExpandArray!(arr[1..$])) ExpandArray;
    }


    static if(Erase!(Max, ExpandArray!(array)).length == 0){
        auto delay(R)(R range)if(isInputRange!R)
        {
            popFrontN(range, array[0]);
            return parallel!(array.length)(range);
        }
    }else{
        

        auto delay(R)(R range)if(isInputRange!R)
        {
            return shred!(ExpandArray!(array))( segment!(Max + 1)(range) );
        }
   }
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4,5];
    auto d = delay!([0,1])(r1); // will iterate on the pair ([0,1,2,3,4,5], [1,2,3,4,5]).
                                // It's equivalent to segment!2(r1)
    assert(equal(d, [tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][]));
    assert(d.length == 5);         // .length
    // back/popBack:
    assert(equal(retro(d), retro([tuple(0,1), tuple(1,2), tuple(2,3), tuple(3,4), tuple(4,5)][])));

    auto d2 = delay!([1,0])(r1); // inverting
    assert(equal(d2, [tuple(1,0), tuple(2,1), tuple(3,2), tuple(4,3), tuple(5,4)][]));

    auto d3 = delay!([0])(r1);   // one element
    assert(equal(d3, [tuple(0), tuple(1), tuple(2), tuple(3), tuple(4), tuple(5)][]));

    auto d4 = delay!([4,1,3,2])(r1); // disjoint extracts
    assert(d4.front == tuple(4,1,3,2));
    assert(d4.length == 2); // d4 is [(4,1,3,2),(5,2,4,3)]

    auto d5 = delay!([0,0,1])(r1); // repeated values
    assert(d5.front == tuple(0,0,1));

    auto d6 = delay!([9,0])(r1);
    assert(d6.empty);

    int[] e;
    assert(delay!([0,1])(e).empty);
}

/**
Another "delay" cousin: takes a number (as template argument) and a range, and produces
a "knit" of n times the same range in parallel.
See_Also: segment, delay.
Example:
----
auto r1 = [0,1,2,3,4,5];
auto p = parallel!4(r1);
assert(equal(p, [tuple(0,0,0,0), tuple(1,1,1,1), tuple(2,2,2,2), tuple(3,3,3,3), tuple(4,4,4,4), tuple(5,5,5,5)][]));
----
*/
/*
Knit!(TypeNuple!(R, n)) parallel(size_t n, R)(R range) if (isForwardRange!R && n > 0){
    TypeNuple!(R, n) temp;
    foreach(i, Unused; temp) temp[i] = range.save;
    return knit(temp);
}
*/

auto parallel(size_t n, R)(R range)if(n > 0 && isInputRange!R)
{
    string createFunc(){
        string dst = "tuple(";
        foreach(Unused; 0..n)
            dst ~= "a,";
        return dst[0..$-1] ~ ")";
    }

    return map!(createFunc())(range);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4,5];
    auto p = parallel!4(r1);
    assert(equal(p, [tuple(0,0,0,0), tuple(1,1,1,1), tuple(2,2,2,2), tuple(3,3,3,3), tuple(4,4,4,4), tuple(5,5,5,5)][]));
}


/**
A simple wrapper to concatenate elements of a range of ranges.
It's equivalent to flatten!1(range), but it's only a forward range.

On a simple range, it has no effect (it's the identity function).

Example:
----
int[][] r1 = [[0,1,2], [3,4], [5]];
auto c = concat(r1);
assert(equal(c, [0,1,2,3,4,5][]));  // from an int[][] to an int[]
assert(equal(retro(c), retro([0,1,2,3,4,5][]))); // bidir range

auto r2 = [0,1,2,3];
auto ror = map!"take(a+1, repeat(a))"(r2); // Equivalent to [[0], [1,1], [2,2,2], [3,3,3,3]]
assert(equal(concat(ror), [0,1,1,2,2,2,3,3,3,3][]));

string sentence = "the quick brown fox jumped over the lazy dog.";
auto words = split(sentence); // a string[], so also a immutable(char)[][]
auto sentence2 = concat(words);
assert(array(sentence2) == "thequickbrownfoxjumpedoverthelazydog.");

assert(equal(concat(c), c));        // c is a simple range, concat(c) has no effect.
----
BUG: doesn"t play so nice with retro. retro.popBack calls concat.popFront, but it seems to have no effect.
*/
struct Concat(R) if (isRangeOfRanges!R)
{
    R _range;
    alias ElementType!R ET0;
    alias ElementType!ET0 ET1;
    ET0 _subrange, _backSubrange;

    this(R range) {
        _range = range;
        if (!_range.empty) {
            _subrange = _range.front;
            while (_subrange.empty && !_range.empty) {
                _range.popFront;
                if (!_range.empty) _subrange = _range.front;
            }
            static if (isBidirectionalRange!R && isBidirectionalRange!ET0) {
                _backSubrange = _range.back;
                while (_backSubrange.empty && !_range.empty) {
                    _range.popBack;
                    if (!_range.empty) _backSubrange = _range.back;
                }
            }
        }
    }

    @property bool empty() {
        return _range.empty;
    }

    @property ET1 front() {
        return _subrange.front;
    }

    @property Concat save() { return this;}

    void popFront() {
        if (!_subrange.empty) _subrange.popFront;

        while (_subrange.empty && !_range.empty) {
            _range.popFront;
            if (!_range.empty) _subrange = _range.front;
        }
    }

    static if (isBidirectionalRange!R && isBidirectionalRange!ET0) {
        ET1 back() {
            return _backSubrange.back;
        }

        void popBack() {
            if (!_backSubrange.empty) _backSubrange.popBack;

            while (_backSubrange.empty && !_range.empty) {
                _range.popBack;
                if (!_range.empty) _backSubrange = _range.back;
            }
        }
    }
}

/// ditto
Concat!R concat(R)(R range) if (isRangeOfRanges!R) {
    return Concat!R(range);
}

/// ditto
R concat(R)(R range) if (isSimpleRange!R) {
    return range;
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    int[][] r1 = [[0,1,2], [3,4], [5]];
    auto c = concat(r1);
    assert(equal(c, [0,1,2,3,4,5][]));
    assert(equal(retro(c), retro([0,1,2,3,4,5][]))); // bidir range

    assert(equal(concat(c), c));

    auto r2 = [0,1,2,3];
    auto ror = map!" std.range.repeat(a, a+1)"(r2); // -> [[0], [1,1], [2,2,2], [3,3,3,3]]
    assert(equal(concat(ror), [0,1,1,2,2,2,3,3,3,3][]));

    string sentence = "the quick brown fox jumped over the lazy dog.";
    auto words = split(sentence); // a string[], so also a immutable(char)[][]
    auto sentence2 = concat(words);
    assert(array(sentence2) == "thequickbrownfoxjumpedoverthelazydog.");

    int[][] ee;
    int[] e;
    assert(concat(ee).empty);
    assert(concat(e).empty);
}

/**
Flatten a range of ranges (of ranges, etc.) n levels deep. n==0 does nothing. n == 1 is just concat(range),
n == 2 is concat(concat(range)), etc. The default is to go for the maximum flattening.
Example:
----
int[][] r1 = [[0,1,2], [3,4], [5]];
auto f = flatten(r1);
assert(equal(f, [0,1,2,3,4,5][]));

int[][][] r2 = [r1, [[6]], r1];
auto f2 = flatten!2(r2);
assert(equal(f2, [0,1,2,3,4,5,6,0,1,2,3,4,5][]));
assert(equal(retro(f2), [5,4,3,2,1,0,6,5,4,3,2,1,0][])); // bidir range

auto f3 = flatten!0(r2); // No flattening -> range unchanged.
assert(equal(f3, r2));

auto f4 = flatten(r2); // go for max flattening. Equals to flatten!2(r2)
assert(equal(f2, f4));

auto f5 = flatten!1(r2); // flatten one level
assert(equal(f5, [[0,1,2], [3,4], [5], [6], [0,1,2], [3,4], [5]][]));
assert(equal(retro(f5), [[5], [3,4], [0,1,2], [6], [5], [3,4], [0,1,2]][]));
----
*/
FlattenType!(n,R) flatten(size_t n = size_t.max, R)(R range) if (isForwardRange!R) {
    static if(n > rank!R)
        return wrapCode!(concat, rank!R, R)(range);
    else
        return wrapCode!(concat, n, R)(range);
}

template FlattenType(size_t n,R)
{
    static if (n > rank!R)
        alias FlattenType!(rank!R,R) FlattenType;
    else static if (n == 0)
        alias R FlattenType;
    else static if (n == rank!R)
        alias FlattenType!(n-1, R) FlattenType;
    else
        alias Concat!(FlattenType!(n-1, R)) FlattenType;
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [[0,1,2], [3,4], [5]];
    auto f = flatten(r1);
    assert(equal(f, [0,1,2,3,4,5][]));
    int[][] r6 = [[6]];

    auto r2 = [r1, r6, r1];
    auto f2 = flatten!2(r2);
    assert(equal(f2, [0,1,2,3,4,5,6,0,1,2,3,4,5][]));
    assert(equal(retro(f2), [5,4,3,2,1,0,6,5,4,3,2,1,0][])); // bidir range

    auto f3 = flatten!0(r2); // No flattening -> range unchanged.
    assert(equal(f3, r2));

    auto f4 = flatten(r2); // go for max flattening. Equals to flatten!2(r2)
    assert(equal(f2, f4));

    auto f5 = flatten!1(r2); // flatten one level
    assert(equal(f5, [[0,1,2], [3,4], [5], [6], [0,1,2], [3,4], [5]][]));
    assert(equal(retro(f5), [[5], [3,4], [0,1,2], [6], [5], [3,4], [0,1,2]][]));
}

/**
Small helper function: given a variadic list of ranges, truncates them to the shortest range's length.
This will modify the input ranges!
Example:
----
auto r1 = [0,1,2,3];
string s = "abcdefghijk";
truncate(r1, s);
assert(r1.length == s.length);
assert(equal(r1, [0,1,2,3][]));
assert(s == "abcd");
----
BUG:
Does not work since DMD 2.04x, when strings were modified. Maybe by using byCodePoint or somesuch?
*/
void truncate(R...)(ref R r) if (allHaveLength!R && !allAreInfinite!R && allSatisfy!(hasSlicing, R))
{
    auto l = minLength(r);
    foreach(i, elem; r) {
        if (!r[i].empty) r[i] = r[i][0..l];
    }
}


unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3];
    auto s = ["a","b","c","d","e","f","g","h","i","j","k"];
    truncate(r1, s);
    assert(r1.length == s.length);
    assert(equal(r1, [0,1,2,3][]));
    assert(s == ["a","b","c","d"]);
}


/**
Emulates the standard Clojure/Python/Ruby function: given a range r,
it will produce an indexed range, with elements tuples(index, element).

If possible, indexed defines back, popBack, length, opIndex and opSlice.
----
auto s = ["a", "b", "c", "d", "e", "f"];
auto e = indexed(s); // (0,"a"), (1,"b"), (2,"c"), (3,"d"), (4, "e"), (5, "f")
assert(e.front == tuple(0, "a"));
assert(e.length == s.length);
e.popFront;
assert(e.front == tuple(1, "b"));
assert(e[3]    == tuple(4, "e")); // opIndex
assert(e.back  == tuple(5, "f")); // back
----
*/
Knit!(Numbers, R) indexed(R)(R range) {
    return knit(numbers(0,int.max,1), range);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto s = ["a", "b", "c", "d", "e", "f"];
    auto e = indexed(s); // (0,"a"), (1,"b"), (2,"c"), (3,"d"), (4, "e"), (5, "f")
    assert(e.front == tuple(0, "a"));
    assert(e.length == s.length);
    e.popFront;
    assert(e.front == tuple(1, "b"));
    assert(e[3]    == tuple(4, "e")); // opIndex
    //assert(e.back  == tuple(5, "f")); // back

    int[] empt;
    assert(indexed(empt).empty);
}

/**
A small range to get the numbers _from from _to to (open at to, it's never reached) with _step step.
0-, 1-, 2- and 3-args version exist, see the examples.
Examples:
----
auto n0 = numbers();            // -> 0,1,2,3,4, ... ,int.max
auto n1 = numbers(10);          // -> 0,1,2,3,4,5,6,7,8,9
auto n2 = numbers(5,10);        // -> 5,6,7,8,9
auto n3 = numbers(1,10,3);      // -> 1,4,7
auto n4 = numbers(1,10,100);    // -> 1
auto n5 = numbers(20,10, -1);   // -> 20,19,18,17,16,15,14,13,12,11
auto n6 = numbers(20,10);       // step defaults to 1 -> empty range
assert(n1[3] == 3);             // opIndex
assert(equal(n1[5..10], n2));   // opSlice
assert(equal(retro(n1), [9,8,7,6,5,4,3,2,1,0][])); // It's a bidirectional range
----
*/
struct Numbers {
    int _num, _max, _step;

    this(int to) pure nothrow @safe { _num = 0; _max = to; _step = 1;}
    this(int from, int to) pure nothrow @safe { _num = from; _max = to; _step = 1;}
    this(int from, int to, int step) pure nothrow @safe { _num = from; _max = to; _step = step;}

    @property bool empty() pure nothrow @safe const { return (_step > 0) ? _num >= _max : _num <= _max;}
    @property int front() pure nothrow @safe const {return _num;}
    @property Numbers save() pure nothrow @safe const { return this;}
    void popFront() pure nothrow @safe { _num = _num + _step;}
    @property int back() pure nothrow @safe const { return _max-1;}
    void popBack() pure nothrow @safe  { _max = _max - _step;}

    int opIndex(size_t index) pure @safe const {
        assert(!((_step > 0) && (index*_step + _num >= _max) || (_step < 0) && (index*_step + _num <= _max)));
        return cast(int)(index*_step + _num);
    }

    Numbers opSlice() const { return this;}

    Numbers opSlice(size_t index1, size_t index2) const {
        if ((_step > 0) && (index1*_step + _num > _max) || (_step < 0) && (index1*_step + _num <= _max))
            throw new Exception("Numbers.opSlice: first index out of bound " ~ to!string(index1*_step) ~ " + " ~ to!string(_num) ~ " >= " ~ to!string(_max));
        if ((_step > 0) && (index2*_step + _num > _max) || (_step < 0) && (index2*_step + _num <= _max))
            throw new Exception("Numbers.opSlice: second index out of bound " ~ to!string(index2*_step) ~ " + " ~ to!string(_num) ~ " >= " ~ to!string(_max));
        return Numbers(to!int(index1*_step + _num), to!int(index2*_step + _num));
    }

    @property size_t length() const { return (this.empty ? 0 : (cast(size_t)((_max-_num)/_step)) + !!((_max - _num)%_step));}
    alias length opDollar;
}

/// ditto
Numbers numbers(int to = int.max) {
    return Numbers(0, to, 1);
}
/// ditto
Numbers numbers(int from, int to, int step = 1) {
    return Numbers(from, to, step);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto n0 = numbers();
    assert(equal(take(n0, 5), [0,1,2,3,4][]));

    auto n1 = numbers(10);
    assert(equal(n1, [0,1,2,3,4,5,6,7,8,9][]));
    assert(n1[3] == 3); // opIndex
    assert(equal(retro(n1), [9,8,7,6,5,4,3,2,1,0][])); // retro

    auto n2 = numbers(5,10);
    assert(equal(n2, [5,6,7,8,9][]));
    assert(equal(n1[5..10], n2)); // slicing

    auto n3 = numbers(1,10,3);
    assert(equal(n3, [1,4,7][]));

    auto n4 = numbers(1,10,100);
    assert(equal(n4, [1][]));

    auto n5 = numbers(20,10, -1);
    assert(equal(n5, [20,19,18,17,16,15,14,13,12,11][]));

    auto n6 = numbers(20,10); // step defaults to 1 -> empty range
    assert(n6.empty);
}

/**
A templated struct for a range of numbers. It can be used with std.bigint, for example.
There is no argument-less version: numberz!BigInt() does not exists (as there is no BigInt.max).
----
auto n1 = numberz(BigInt("1000000000000000"), BigInt("2000000000000000"));
    // -> 1000000000000000, 1000000000000001, 1000000000000002, 1000000000000003, ..., 1000000000000010
assert(n1[3] == BigInt("1000000000000003")); // opIndex with standard index
assert(n1[BigInt("500000000000000")] == BigInt("1500000000000000")); // Indexed with BigInt too
assert(n1.length == BigInt("1000000000000000")); // .length returns a BigInt
----
*/
struct Numberz(T) {
    T _num, _max, _step;

    this(T to) { _num = 0; _max = to; _step = 1;}
    this(T from, T to) { _num = from; _max = to; _step = 1;}
    this(T from, T to, T step) { _num = from; _max = to; _step = step;}

    @property bool empty() const { return (_step > 0) ? _num >= _max : _num <= _max;}
    @property T front() const {return _num;}
    @property Numberz save() const { return this;}
    void popFront() { _num = _num + _step;}
    @property T back() const { return _max - _step;}
    void popBack()  { _max = _max - _step;}

    static if (!is(T == size_t)) T opIndex(size_t index) { T i = index; return opIndex(i);}

    T opIndex(T index) const {
        T i = index*_step + _num;
        if ((i < 0) || (_step > 0) && (i >= _max) || (_step < 0) && (i <= _max))
            throw new Exception("Numberz!" ~ T.stringof ~ ".opIndex: Out of bound with index: " ~ to!string(index));
        return i;
    }

    Numberz!T opSlice() const { return this;}

    Numberz!T opSlice(T index1, T index2) const {
        T i1 = index1*_step + _num;
        T i2 = index2*_step + _num;
        if ((i1 < 0) || (_step > 0) && (i1 > _max) || (_step < 0) && (i1 < _max))
            throw new Exception("Numberz!" ~ T.stringof ~ ".opSlice: first index out of bound " ~ to!string(i1) ~ " >= " ~ to!string(_max));
        if ((i2 < 0) || (_step > 0) && (i2 > _max) || (_step < 0) && (i2 < _max))
            throw new Exception("Numberz!" ~ T.stringof ~ ".opSlice: second index out of bound " ~ to!string(i2) ~ " >= " ~ to!string(_max));
        return Numberz!T(i1, i2, _step);
    }

    T length() const { return (empty ? T.init : (_max-_num)/_step);}
    alias length opDollar;
}

/// ditto
Numberz!T numberz(T)(T to) {
    return Numberz!T(cast(T)0, to, cast(T)1);
}

/// ditto
Numberz!T numberz(T)(T from, T to, T step) {
    return Numberz!T(from, to, step);
}

/+
unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto n1 = numberz(BigInt("1000000000000000"), BigInt("2000000000000000"), BigInt("1"));
    // -> 1000000000000000, 1000000000000001, 1000000000000002, 1000000000000003, ..., 1000000000000010
    assert(n1[3] == BigInt("1000000000000003"));
    assert(n1[BigInt("500000000000000")] == BigInt("1500000000000000"));
    assert(n1.length == BigInt("1000000000000000"));
}
+/

/**
Simple range producing all natural numbers, alternating
between positive and negative numbers: 0, 1, -1, 2, -2, 3, -3, ...
*/
struct NaturalNumbers {
    long _num = 0;
    bool _positive = true;
    enum bool empty = false;
    @property long front() pure nothrow const @safe { return _num;}
    @property NaturalNumbers save() pure nothrow const @safe { return this;}
    void popFront() pure nothrow @safe {
        if (_num == 0) {
            _num = 1;
            return;
        }
        if (_positive) {
            _num *= -1;
            _positive= false;
        }
        else {
            _num = -_num +1;
            _positive = true;
        }
    }
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    assert(equal(take(NaturalNumbers(), 7), [0,1,-1,2,-2,3,-3][]));
}

/**
An empty range. Its element type is parameterized by T, to enable compatibility
(for ranges which check front's type).

----
auto e = emptyRange!int; //uses the helper function. Otherwise: auto e = EmptyRange!int();
assert(e.empty);
assert(e.length == 0);
assert(asString(e) == "");
assert(is(ElementType!(typeof(e)) == int));
assert(isInputRange!(typeof(e)));
assert(isForwardRange!(typeof(e)));
assert(isBidirectionalRange!(typeof(e)));
assert(isRandomAccessRange!(typeof(e)));
assert(hasLength!(typeof(e)));
assert(hasSlicing!(typeof(e)));
----
*/
struct EmptyRange(T) {
    enum bool empty = true;
    enum size_t length = 0;
    @property size_t opDollar() @safe pure nothrow const {return 0;}
    @property EmptyRange save() @safe pure nothrow const { return this;}
    void popFront() @safe pure const {throw new Exception("EmptyRange is empty: do not call popFront");}
    @property T front() @safe pure const {throw new Exception("EmptyRange is empty: do not call front"); /*return T.init;*/ }
    void popBack() pure @safe const {throw new Exception("EmptyRange is empty: do not call popBack");}
    @property T back() pure @safe const {throw new Exception("EmptyRange is empty: do not call back"); /*return T.init;*/}
    T opIndex(size_t index) pure @safe const {throw new Exception("EmptyRange is empty: do not call opIndex"); /*return T.init;*/}
    EmptyRange!T opSlice(size_t index1, size_t index2) pure nothrow @safe const {return this;}

    R opCat(R)(R range)if (isForwardRange!R && is(ElementType!R == T)){ return range;}
    R opCat_r(R)(R range)if (isForwardRange!R && is(ElementType!R == T)){ return range;}
}

/// ditto
EmptyRange!T emptyRange(T)() {
    return EmptyRange!T();
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto e = emptyRange!int; //uses the helper function. Otherwise: auto e = EmptyRange!int();
    assert(e.empty);
    assert(e.length == 0);
    assert(asString(e) == "");
    static assert(is(ElementType!(typeof(e)) == int));

    static assert(isInputRange!(typeof(e)));
    static assert(isForwardRange!(typeof(e)));
    static assert(isBidirectionalRange!(typeof(e)));
    static assert(isRandomAccessRange!(typeof(e)));
    static assert(hasLength!(typeof(e)));
    static assert(hasSlicing!(typeof(e)));

    auto arremp = emptyRange!(int[]);
}

/**
A one-element range. This element is defined at creation and will be produced once. The range is then empty.
----
auto e = once(1.1);
assert(e.front == 1.1);
assert(e.length == 1);
assert(asString(e) == "1.1");
e.popFront;
assert(e.empty);
----
*/
struct Once(T) {
    bool _empty = true;
    T elem;
    this(T value) pure nothrow @safe {elem = value; _empty = false;}

    @property bool empty() pure nothrow @safe const { return _empty;}
    @property T front() pure @safe { return elem;}
    @property Once save() pure nothrow @safe{
        return this;
    }
    void popFront() pure nothrow @safe { _empty = true;}
    @property T back() pure nothrow @safe{ return elem;}
    void popBack() pure nothrow @safe { _empty = true;}
    @property size_t length() pure nothrow @safe const {return _empty ? 0 : 1;}
    alias length opDollar;
    ref T opIndex(size_t index) pure @safe{ assert(index == 0); return elem;}
    void opIndexAssign(T value, size_t index) pure @safe { assert(index == 0); elem = value;}
    Once opSlice() pure @safe nothrow{ return this;}
/+    Once!T opSlice(ulong i1, ulong i2) // strange, I had to put ulong to satisfy std.range.ChainImpl
    {
        assert(i1 <= this.length()); // It was originally == 0, but [1..1] seems authorized for arrays. I thought it wasn"t.
        assert(i2 <= this.length());
        auto slice = this;
        if (i1 == i2 && !slice.empty) slice.popFront;
        return slice;
    }+/

    mixin Chainable!();
}

/// ditto
Once!T once(T)(T value) {
    return Once!T(value);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto e = once(1.1);
    assert(e.front == 1.1);
    assert(e.length == 1);
    assert(asString(e) == "1.1");
    e.popFront;
    assert(e.empty);
}

/**
An infinite range giving the digits of pi, in base 10 (as ints).
Example:
----
auto pi = take(piDigits, 10);
assert(equal(pi, [3,1,4,1,5,9,2,6,5,3]));
----
It has a reasonable speed up to a few thousands digits, but slows down sharply afterwards.
On my machine: 1000 digits: 100 ms, 3000 digits: 300 ms, 10_000 digits: 2.4 s, 30_000 digits: 22 s
*/
struct Pi
{
    BigInt q,r,t,i,u,y;
    enum bool empty = false;
    @property int front() const { return to!int(y.toInt());}
    @property Pi save() { return this;}
    void popFront()
    {
        r = BigInt(10)*u*(q*(BigInt(5)*i-BigInt(2)) +r-y*t);
        q = BigInt(10)*q*i*(BigInt(2)*i-BigInt(1));
        t = t*u;
        i = i + BigInt(1);
        u = BigInt(3)*(BigInt(3)*i+BigInt(1))*(BigInt(3)*i+BigInt(2));
        y = (q*(BigInt(27)*i-BigInt(12))+BigInt(5)*r)/(BigInt(5)*t);
    }
}

/// ditto
Pi piDigits()
{
    return Pi(BigInt(1),BigInt(180),BigInt(60),BigInt(2),BigInt(3*7*8),BigInt(3));
}

/**
It's an infinite bidirectional range: a range that has infinitely many values,
but knows its end:

n0 n1 n2 ... (infinitely many values)  ... m2 m1 m0

It's in fact a completly standard infinite bidirectional range, modelized with two (non-bidir) infinite ranges.
*/
struct InfiniteBiDir(R1, R2) if (isForwardRange!R1 && isForwardRange!R1
                                 && isInfinite!R1 && isInfinite!R2
                                 && !isBidirectionalRange!R1 && !isBidirectionalRange!R2
                                 && CompatibleRanges!(R1,R2))
{
    R1 _r1;
    R2 _r2;
    alias CommonElementType!(R1,R2) ET;

    this(R1 r1, R2 r2) { _r1 = r1; _r2 = r2;}

    enum bool empty = false;

    @property ET front() { return _r1.front;}
    @property InfiniteBiDir save() { return this;}
    void popFront() { _r1.popFront;}
    @property ET back() { return _r2.front;}
    void popBack() { _r2.popFront;}

    static if (isRandomAccessRange!R1 && isRandomAccessRange!R2)
    {
        ET opIndex(long i)
        {
            return (i>=0) ? _r1[i] : _r2[-i-1];
        }
    }

    typeof(this) opSlice() { return this;}

    // slicing like s[2..10] or even s[2..-2] would be nice, but there is a type pb: the types are different
    // (R1 for the first, InfBiDir!(R1,R2) for the second. And it's not possible to change types on the run-time values of indices.

}

InfiniteBiDir!(R1,R2) infiniteBiDir(R1,R2)(R1 r1, R2 r2)
{
    return InfiniteBiDir!(R1,R2)(r1,r2);
}

/**
Replicates a range n times. back, popBack, length and opIndex will be defined
if the subjacent R permits it.
Example:
----
auto r1 = [0,1,2,3];
auto r2 = replicateRange(r1, 3);
assert(equal(r2, [0,1,2,3,0,1,2,3,0,1,2,3][]));
assert(r2.length == r1.length * 3);
assert(r2[3] == 3);

r2.popFront;
r2.popBack;
assert(equal(r2, [1,2,3,0,1,2,3,0,1,2][])); // You can truncate it at both ends
assert(r2.length == r1.length * 3 - 2); // length update
assert(r2[3] == 0); // Indexing is always 0-based, of course.

assert(replicateRange(r1, 0).empty); // if n == 0, replicateRange is an empty range
assert(equal(replicateRange(r1, 1), r1));
----
*/
struct ReplicateRange(R) if (isForwardRange!R) {
    R _range, _copy, _backCopy; // _backCopy is used only with bidirectional ranges
    uint _times;

    this(R range, uint n) {
        _range = range;
        _copy = range;
        _backCopy = range;
        _times = n;
    }

    @property bool empty() { return (_times == 0 || _range.empty);}

    @property ReplicateRange save() { return this;}

    void popFront() {
        _copy.popFront;
        if (_copy.empty) {
            _times--;
            _copy = _range;
            if (_times <= 1) { // the two extremities are working on the same sub-range: need to coordinate them
                static if (isBidirectionalRange!R) { // back exists, _copyBack is used
                    _copy = _backCopy;
                }
            }
        }
    }

    @property ElementType!R front() { return _copy.front;}

    static if (isBidirectionalRange!R) {
        void popBack() {
            if (_times > 1) {
                _backCopy.popBack;
                if (_backCopy.empty) {
                    _times--;
                    _backCopy = _range;
                }
            }
            else { // the two extremities are working on the same sub-range: we need to coordinate them
                _copy.popBack;
                if (_copy.empty) {
                    _times--;
                    _copy = _range;
                }
                _backCopy = _copy;
            }
        }

        ElementType!R back() { return _backCopy.back;}
    }

    static if (hasLength!R) {
        @property size_t length() {
            switch (_times) {
                case 0:
                    return 0;
                case 1:
                    return _range.length * _times + (_copy.length - _range.length);
                default:
                    return _range.length * _times + (_copy.length - _range.length) + (_backCopy.length - _range.length);
            }
        }
        alias length opDollar;
    }

    static if (isRandomAccessRange!R && hasLength!R) { // and hasLength...
        ElementType!R opIndex(size_t index) {
            long i = (cast(long)index + _range.length - _copy.length) / _range.length;
            if (i == 0) return _copy[index];
            if (i == _times -1) return _backCopy[(index + _range.length - _copy.length) % _range.length];
            return _range[(index + _range.length - _copy.length) % _range.length];
        }
    }
}

/// ditto
auto replicateRange(R)(R range, uint n = 1) if (isForwardRange!R) {
    return ReplicateRange!(R)(range, n);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3];
    auto r2 = replicateRange(r1, 3);
    assert(equal(r2, [0,1,2,3,0,1,2,3,0,1,2,3][]));
    assert(r2.length == r1.length * 3);
    assert(r2[3] == 3);

    r2.popFront;
    r2.popBack;
    assert(equal(r2, [1,2,3,0,1,2,3,0,1,2][])); // You can truncate it at both ends
    assert(r2.length == r1.length * 3 - 2); // length update
    assert(r2[3] == 0); // Indexing is always 0-based, of course.

    assert(replicateRange(r1, 0).empty); // if n == 0, replicateRange is an empty range
    assert(equal(replicateRange(r1, 1), r1));

    auto e = emptyRange!int();
    assert(replicateRange(e, 10).empty); // Replicating an empty range: still just an empty range.
}

/**
Repeat n times each element of a range. If the input is a bidirectional range,
stutter will also be one (defines back and popBack), the same for a random-access range.
Also, if input has a length, stutter will have one.
Example:
----
auto r1 = [0,1,2,3];
string s = "abc";
auto st1 = stutter(r1, 3);
auto st2 = stutter(s, 2);
assert(st1.length == r1.length * 3);
assert(equal(st1, [0,0,0,1,1,1,2,2,2,3,3,3][]));
assert(equal(st2, "aabbcc")); // Works on strings, too.
//
st1.popFront;
st1.popBack;
assert(equal(st1, [0,0,1,1,1,2,2,2,3,3][]));
assert(st1.length == r1.length * 3 - 2);            // length update
assert(equal(retro(st1), [3,3,2,2,2,1,1,1,0,0][])); // Bidirectional range
assert(st1[2] == 1);                                // Random-access range
//
assert(stutter(r1, 0).empty);                       // stutter(_,0) -> empty
auto e = emptyRange!int;
assert(stutter(e, 3).empty);                        // stutter(empty, n) -> empty
assert(equal(stutter(r1,1), r1));                   // stutter(r,1) -> r
----
*/
struct Stutter(R) if (isForwardRange!R){
    R _range;
    uint _times, _frontCount, _backCount;

    this(uint times, R range) {
        _range = range;
        _times = times;
        _frontCount = times;
        _backCount = times;
    }

    @property bool hasOneElement() {
        return walkLength(_range, 2) == 1;
    }

    @property bool empty() {
        return (_range.empty || _frontCount == 0 || _backCount == 0); // If _count is zero at creation -> empty range.
                                                      // Else it will become zero once _range is empty.
    }

    @property Stutter save() { return this;}

    void popFront() {
        if (_frontCount <= 1) {
            if (!_range.empty) _range.popFront;
            // One-element -> 0 element:
            _frontCount = _range.empty ? 0 : _times;
            if (hasOneElement()) _frontCount = _backCount;
        }
        else {
           _frontCount--;
        }
    }

    @property ElementType!R front() {
        return _range.front;
    }

    static if (hasLength!R) {
        @property size_t length() {
            return   _range.length * _times
                   - (_times - _frontCount)
                   - (_times - _backCount);
        }

        alias length opDollar;
    }

    static if (isBidirectionalRange!R) {
        void popBack() {
            if (_backCount <= 1) {
                if (!_range.empty) _range.popBack;
                // One-element -> 0 element:
                _backCount = _range.empty ? 0 : _times;
                if (hasOneElement()) _backCount = _frontCount;
            }
            else {
                _backCount--;
            }
        }

        @property ElementType!R back() {
            return _range.back;
        }
    }

    static if (isRandomAccessRange!R) {
        ElementType!R opIndex(size_t index) {
            size_t idx = (index + _times - _frontCount);
            static if (hasLength!R) {
                if (idx > this.length +1) {
                    throw new Exception("stutter.opIndex: Out of range. index: " ~ to!string(idx) ~ " max: " ~ to!string(this.length +1));
                }
            }
            return _range[idx / _times];
        }
    }
}

/// ditto
Stutter!(R) stutter(R)(uint n, R range)
{
    return Stutter!(R)(n, range);
}

/**
Another version, based on flatMap.
----
flatMap!(format("array(repeat(a, %s))", n))(r);
----
It's a one-liner, but it's a forward range, no more (no opIndex, back, etc)
*/
Concat!(Map!(unaryFun!(format("array(repeat(a, %s))", n)), R)) stutter2(size_t n, R)(R r) if (isForwardRange!R)
{
    return flatMap!(Format!("array(repeat(a, %s))", n))(r);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3];
    string s = "abc";
    auto st1 = stutter(3, r1);
    auto st2 = stutter(2, s);
    assert(st1.length == r1.length * 3);
    assert(equal(st1, [0,0,0,1,1,1,2,2,2,3,3,3][]));
    assert(equal(st2, "aabbcc")); // Works on strings, too.

    st1.popFront;
    st1.popBack;
    assert(equal(st1, [0,0,1,1,1,2,2,2,3,3][]));
    assert(st1.length == r1.length * 3 - 2); // length update
    assert(equal(retro(st1), [3,3,2,2,2,1,1,1,0,0][])); // Bidirectional range
    assert(st1[2] == 1); // Random-access range

    assert(stutter(0, r1).empty); // stutter(_,0) -> empty
    int[] e;
    assert(stutter(3, e).empty);
    assert(equal(stutter(1, r1), r1)); // stutter(r,1) -> r
}

/**
A forward range which alternates between input's two extremities. It's a kind of dual to std.range.radial.
Example:
----
auto r1 = [0,1,2,3,4,5,6];
auto ext = extremities(r1);
assert(ext.length == r1.length); // length is defined
assert(equal(ext, [0,6,1,5,2,4,3][]));
assert(extremities(emptyRange!int).empty); // extremities on an empty range -> empty
----
*/
struct Extremities(R) if (isBidirectionalRange!R) {
    R _range;
    uint _state;

    this(R range) {
        _range = range;
        _state = 0;
    }

    @property bool empty() {
        return _range.empty;
    }

    @property ElementType!R front() {
        return _state == 0 ? _range.front : _range.back;
    }

    @property Extremities save() { return this;}

    void popFront() {
        if (_state == 0) {
            _range.popFront;
        }
        else {
            _range.popBack;
        }
        _state = 1 - _state;
    }

    static if (hasLength!R) {
        @property size_t length() {
            return _range.length;
        }

        alias length opDollar;
    }
}

/// ditto
Extremities!R extremities(R)(R range) {
    return Extremities!(R)(range);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4,5,6];
    auto ext = extremities(r1);
    assert(ext.length == r1.length); // length is defined
    assert(equal(ext, [0,6,1,5,2,4,3][]));
    assert(equal(extremities(r1[0..1]), r1[0..1])); // One element range -> One element range
    int[] e;
    assert(extremities(e).empty); // extremities on an empty range -> empty
}


/**
Iterate on a bidirectional range by going back and forth between its extremities.
Example:
----
auto r = [0,1,2,3];
auto b = bounce(r);
assert(equal(take(b, 10), [0,1,2,3,2,1,0,1,2,3][]));

auto r2 = [1];
assert(equal(take(bounce(r2), 10), repeat(1, 10))); // 1,1,1,1,...
----
*/
auto bounce(R)(R range) if (isBidirectionalRange!R)
{
    auto r = range;
    if (!r.empty) r.popFront;
    if (!r.empty) r.popBack;
    return cycle(chain(range, retro(r)));
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r = [0,1,2,3];
    auto b = bounce(r);
    assert(equal(take(b, 10), [0,1,2,3,2,1,0,1,2,3][]));

    auto r2 = [1];
    assert(equal(take(bounce(r2), 10), std.range.repeat(1, 10)));
}

/**
Produces a range with elements of r1 without those of r2. Equivalent to Haskell (\\).
By default, each element of r2 is used only once. With the boolean option cyclic set to true,
you get without(r1, cycle(r2)) and all occurences of an element of r2 in r1 are dropped.
Example:
----
auto r1 = [0,1,2,3,4,5,6,2,3,4];

without(r1, [2,3,4][]);         // [0,1,5,6,2,3,4][] getting rid of 2,3,4. Those at the end are still there
without(r1, [2,3,4,2,3][]);     // [0,1,5,6,4][] 2,3 at the end are eliminated
without(r1, [2,3,4][], true);   // [0,1,5,6][] eliminate all 2, 3 and 4 from r1.
without("banana", "a", true);   // "bnn"
without(r1, numbers(), true);   // (int[]).init (empty range) all are numbers eliminated from r1

r1.without([2,3,4][]);          // For arrays, you can also use an infix syntax
"banana".without("a", true);
----
*/
struct Without(R1, R2)
{
    R1 _range1;
    R2 _range2;
    bool _cyclic;

    this(R1 range1, R2 range2, bool cyclic = false) {
        _range1 = range1;
        _range2 = range2;
        _cyclic = cyclic;
        while (!_range1.empty && !_range2.empty && /*isOneOf!(_range2)(_range1.front)*/ !_range2.find(_range1.front).empty) {
            _range1.popFront;
            if (!_cyclic) _range2.popFront;
        }
    }

    @property bool empty() { return _range1.empty;}

    @property ElementType!R1 front() { return _range1.front;}

    @property Without save() { return this;}

    void popFront() {
        _range1.popFront;
        while (!_range1.empty && !_range2.empty && /*isOneOf!(_range2)(_range1.front)*/ !_range2.find(_range1.front).empty) {
            _range1.popFront;
            if (!_cyclic) _range2.popFront;
        }
    }
}

/// ditto
Without!(R1,R2) without(R1, R2)(R1 range1, R2 range2, bool cyclic = false) {
    return Without!(R1,R2)(range1, range2, cyclic);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4,5,6,2,3,4];

    assert(equal(without(r1, [2,3,4][]),[0,1,5,6,2,3,4][])); // getting rid of 2,3,4. Those at the end are still there
    assert(equal(without(r1, [2,3,4,2,3][]),[0,1,5,6,4][])); // 2,3 at the end are eliminated
    assert(equal(without(r1, [2,3,4][], true),[0,1,5,6][])); // eliminate all 2, 3 and 4 from r1.
    assert(equal(without("banana", "a", true), "bnn"));
    assert(without(r1, numbers(), true).empty);

    int[] e;
    assert(equal(without(r1, e), r1)); // eliminating nothing -> get r1 back
    assert(without(e, [2,3,4][]).empty); // eminating something from an empty range -> get an empty range
}


/**
Helper struct to transform a range into a set. Each value is memoized when first output
and then filtered. AsSet has no way to know if all values have been created, so on an infinite range
it may never stop, looking for a nth new value which will never come. AsSet does know
about std.range periodic ranges (Cycle and Repeat) and extract the internal value.
Example:
----
asSet([0,1,2,2,3,3,4,5,5,6,9,1,2,4,9][]); // 0,1,2,3,4,5,6,9, OK.
asSet(cycle([4,5,6][])); // 4,5,6
----
*/
struct AsSet(R) if (isForwardRange!R) {
    R _range;
    bool[ElementType!R] elements;

    this(R range) { _range = range;}
    @property bool empty() {return _range.empty;}
    @property AsSet save() { return this;}
    void popFront() { while(!_range.empty && (_range.front in elements) ) _range.popFront;}

    @property ElementType!R front() {
        auto f = _range.front;
        elements[f] = true;
        return f;
    }
}

///// ditto
//struct AsSet(R : Cycle!U, U)
//{
//    bool[ElementType!U] elements; // Necessary, as the original range may have repeated values
//    U _range;

//    this(R range) { _range = range._original;}
//    @property bool empty() {return _range.empty;}
//    @property AsSet save() { return this;}
//    void popFront() {
//        _range.popFront;
//        while(!_range.empty && (_range.front in elements)) _range.popFront;
//    }

//    @property ElementType!R front() {
//        auto f = _range.front;
//        elements[f] = true;
//        return f;
//    }
//}

///// ditto
//struct AsSet(R : Repeat!U, U)
//{
//    U[] _range;

//    this(R range) { if (!range.empty) _range = [range.front][];} // or else range is an empty Repeat. I don"t think that's even possible.
//    @property bool empty() {return _range.empty;}
//    @property AsSet save() { return this;}
//    void popFront() { _range.popFront;}
//    @property ElementType!R front() { return _range.front;}
//}

/// ditto
AsSet!R asSet(R)(R range)
{
    return AsSet!(R)(range);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    assert(equal(asSet([0,0,1,2,2,3,3,4,5,5,6,9,1,2,4,9][]), [0,1,2,3,4,5,6,9][]));
    assert(equal(asSet(take(cycle([4,5,6][]), 1000)), [4,5,6][]));
    //assert(equal(asSet(cycle([4,5,6][])), [4,5,6][]));
    //assert(equal(asSet(cycle([4,5,6,5][])), [4,5,6][]));
    //assert(equal(asSet(repeat(4)), [4][]));
    int[] e;
    assert(asSet(e).empty);
}

/+
/**
Calculates the smallest length on a variadic list of ranges. Any range not defining
length is skipped.
Usage:
----
auto r1 = [0,1,2,3,4];
string s = "abc";
auto c = cycle([0,1,2,3]);
auto l = smallestLength(r1,s,c);
assert(l == s.length); // c doesn"t count, it's infinite.
----
*/
size_t smallestLength(R, Rest...)(R range0, Rest rest) {
    return smallestLengthImpl(size_t.max, range0, rest);
}

size_t smallestLengthImpl(R, Rest...)(size_t currentLength, R range0, Rest rest) {
    static if (hasLength!R) {
        size_t r0Length = range0.length;
        if (r0Length < currentLength) currentLength = r0Length;
    }
    static if (Rest.length > 0) {
        return smallestLengthImpl(currentLength, rest);
    }
    else {
        return currentLength;
    }
}

unittest {
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4];
    string s = "abc";
    auto c = cycle([0,1,2,3][]);
    auto l = smallestLength(r1,s,c);
    assert(l == s.length); // c doesn"t count, it's infinite.
}
+/

/**
Simple wrapper range to cache the front and back elements of another range.
*/
struct Cache(R) if (isForwardRange!R)
{
    R _input;
    ElementType!R _front, _back;

    this(R input) {
        _input = input;
        if (!_input.empty) _front = _input.front;
        static if (isBidirectionalRange!R)
            if (!_input.empty) _back = _input.back;
    }

    @property bool empty() { return _input.empty;}
    @property ElementType!R front() { return _front;}
    @property Cache save() { return this;}
    void popFront() { _input.popFront; if (!_input.empty) _front = _input.front;}
    static if (isBidirectionalRange!R) {
        @property ElementType!R back() { return _back;}
        void popBack() { _input.popBack; if (!_input.empty) _back = _input.back;}
    }

    static if (hasLength!R){
        size_t length() { return _input.length;}
        alias length opDollar;
    }
}

/// ditto
Cache!R cache(R)(R r) if (isForwardRange!R) {
    return Cache!(R)(r);
}

/**
To iterate on range using a function with side-effects. It doesn"t use the return values,
so it acts only through fun's side-effects. Mainly used to print a range.
----
auto r1 = [0,1,2,3,4];
forEach!(write)(r1); // writes "01234"
int sum;
forEach!((int a){sum += a;})(r1);
assert(sum == reduce!"a+b"(r1)); // sum contains 0+1+2+3+4
----
*/
void forEach(alias fun, R)(R range) if (isInputRange!R) {
    alias unaryFun!fun func;
    foreach(ref elem; range) func(elem);
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3,4];
    int sum;
    forEach!((int a){sum += a;})(r1);
    assert(sum == reduce!"a+b"(r1)); // sum now contains 0+1+2+3+4
}

/**
Greedily iterates on range and returns a string with all range elements
separated by sep. An overload exists, with three string parameters controlling
the beginning of the string, the separator and the end.
Example:
----
auto r1 = [0,1,2,3];
string r2 = "abcdef";
assert(asString(r1) == "0123");
assert(asString(r2) == r2);
assert(asString(r2, ",") == "a,b,c,d,e,f");
assert(asString(r2, "[", "-", "]") == "[a-b-c-d-e-f]");
----
*/
string asString(R)(R range, string sep = "") if (isInputRange!R) {
    if (range.empty) {
        return "";
    }
    else {
        string res;
        foreach(elem; range) res ~= to!string(elem) ~ sep;
        popBackN(res, sep.length);
        return res; // getting rid of the last sep
//        return reduce!((a,b){ return a ~ sep ~ b;})(map!"to!string(a)"(range));
    }
}

/// ditto
string asString(R)(R range, string pre, string sep, string post) if (isInputRange!R) {
    if (range.empty) {
        return pre ~ post;
    }
    else {
        string res = pre;
        foreach(elem; range) res ~= to!string(elem) ~ sep;
        popBackN(res, sep.length); // getting rid of the last sep
        return res ~ post;
    }
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = [0,1,2,3];
    string r2 = "abcdef";
    double[] r3;
    assert(asString(r1) == "0123");
    assert(asString(r2) == r2);
    assert(asString(r3) == "");
    assert(asString(r2, ",") == "a,b,c,d,e,f");
    assert(asString(r2, "[", "-", "]") == "[a-b-c-d-e-f]");
    assert(asString("", "[", "-", "]") == "[]");
    assert(asString("a", "[", "-", "]") == "[a]");
}

/**
Small utility function to print a range. Mainly used for debugging/testing purposes.
*/
void wr(R)(R range, string sep = " ") if (isInputRange!R && !isRangeOfRanges!R) {
    writeln((ElementType!(typeof(range))).stringof, ": ", asString(range, sep));
}

/// ditto
void wr(R)(R range, string pre, string sep, string post) if (isInputRange!R && !isRangeOfRanges!R) {
    writeln((ElementType!(typeof(range))).stringof, ": ", asString(range, pre, sep, post));
}

/// ditto
void wr(R)(R range, string sep = " ") if (isRangeOfRanges!R) {
    writeln((ElementType!(typeof(range))).stringof, ":");
    foreach(elem; range) wr(elem, sep);
}

/**
A template to mixin to get some catenation operations defined on a range, based
on std.range.chain. If r1 is a range with mixin(Chainable!()), r2 a range with
the same element type, and e an element, you can do:
----
r1 ~ r2; // Concatenation on the right.
e[] ~ r1;// Concatenation on the left with an array of elements.
r1 ~ e;  // concatenation on the right with a new element.
e ~ r1;  // concatenation on the left with a new element.
----
What you don"t get is:
----
r2 ~ r1; // No, r2 must define opCat. A templated opCat_r does not work if r1 and r2 both define it and opCat.
----
Note: it detects Chain!R and reacts accordingly. That is, it does not build Chain!(R, Chain!(U)), but Chain!(R,U).
Note: to be really interesting, it needs some modifications of std.range.Chain, to give it opCat capabilities.
*/
mixin template Chainable() /+if (isInputRange!T)+/ {
    alias ElementType!(typeof(this)) ETthis;

    // Concat to the right with another range.
    Chain!(typeof(this), R) opCat(R)(R r) if (!is(ETthis == R) && isInputRange!R && !is(R.RvalueElementType) && is(ETthis == ElementType!R)) {
        return chain(this, r);
    }

    // Concat to the right with a chain.
    Chain!(typeof(this), U) opCat(U...)(ChainImpl!U r) if (is(ETthis == ElementType!(ChainImpl!U))) {
        return chain(this, r._input.expand);
    }
    // Concat to the left with an array
    auto opCat_r(ETthis[] t) {
        return chain(t, this);
    }
    // Concat to the right with an element
    Chain!(typeof(this), R[]) opCat(R)(R e) if (is(ETthis == R)) {
        return chain(this, [e][]);
    }
    // Concat to the left with an element
    auto opCat_r(ETthis e) {
        return chain([e][], this);
    }
}

///
T[] append(T,E)(T[] array, E elem) if (isImplicitlyConvertibleTo!(E,T))
{
    return array ~ elem;
}

///
T[] prepend(T,E)(T[] array, E elem) if (isImplicitlyConvertibleTo!(E,T))
{
    return elem ~ array;
}

///
auto distribute(alias operation = tuple, R1, R2)(R1 r1, R2 r2) if (isForwardRange!R1 && isForwardRange!R2)
{
    return tmap!operation(combinations(r1,r2));
}

///
auto mapFunRange(R, E)(R rangeOfFuns, E elem) if (isForwardRange!R && is(ParameterTypeTuple!(ElementType!R) == TypeTuple!E))
{
    return tmap!("a(b)")(rangeOfFuns, repeat(elem));
}

/**
A sort-of extension of standard ranges that remembers the previous values output through
front and back and can deliver them anew. The front can go back with retreat and the back
can "go forward" with advance. Use asNew/backAsNew to see if you can still retreat/advance.
BUG: doesn"t quite work. I"m getting fed up with this: too many internal states to consider. I should
tackle this anew.
*/
struct Store(R) if (isInputRange!R)
{
    R _range;
    ElementType!R[] store;
    int index;
    // For Bidirectional ranges only:
    ElementType!R[] backStore;
    int backIndex;

    this(R range) { _range = range;}

    static if (isInfinite!R)
        enum bool empty = false;
    else
        @property bool empty() { return _range.empty && (index == store.length && backIndex == backStore.length);}

    @property ElementType!R front()
    {
        if (usingStore)
        {
            return store[index];
        }
        else
        {
            return (exhausted) ? backStore.front : _range.front;
        }
    }

    @property Store save() { return this;}

    void popFront()
    {
        if (usingStore)
        {
            if (index == store.length) // "empty store". If we are using popFront, it means Store is not empty. So backStore is not empty.
            {
                store ~= backStore.back; // transfer one element from backStore to store.
                backStore.popBack;
                ++index;
                if (backIndex == backStore.length -1) --backIndex;
            }
            else
            {
                ++index;
            }
        }
        else
        {
            store ~= _range.front;
            ++index;
            _range.popFront;
        }
    }

    bool asNew() { return (index == 0 && store.length == 0) || index < 0;}
    bool usingStore() { return 0 <= index && index < store.length;}
    void retreat() { --index;}

    bool usingBackStore() { return 0 <= backIndex && backIndex < backStore.length;}
    bool backAsNew() { return (backIndex == 0 && backStore.length == 0) || backIndex < 0;}
    void advance() { backIndex--;} // backRetreat?
    bool exhausted() { return _range.empty;}

    static if (hasLength!R){
        @property size_t length() { return _range.length + (store.length - index) + (backStore.length - backIndex);}
        alias length opDollar;
    }

    static if (isBidirectionalRange!R) {

// Mmm, what if I call back, popBack and back again? Same value?
        @property ElementType!R back() {
            if (usingBackStore)
            {
                return backStore[backIndex];
            }
            else
            {
                return (exhausted) ? store.back : _range.back;
            }
        }

        void popBack()
        {
            if (usingBackStore)
            {
                if (backIndex == backStore.length - 1) // relay passing. Take one element from store, give it to backStore
                {
                    backStore ~= store.back;
                    store.popBack;
                    ++backIndex;
                    if (index == store.length) --index; // invariant conservation
                }
                else
                {
                    ++backIndex;
                }
            }
            else
            {
                backStore ~= _range.back;
                backIndex++;
                _range.popBack;
            }
        }

    }

    static if (isRandomAccessRange!R) {
        ElementType!R opIndex(size_t i) {
            return (usingStore) ? store[index+i] : _range[i];
        }

        static if (hasAssignableElements!R) {
            void opIndexAssign(ElementType!R e, size_t i) {
                if (usingStore) {
                    store[index+i] = e;
                }
                else {
                    _range[i] = e;
                }
            }
        }
    }

}

Store!R store(R)(R range) if (isInputRange!R)
{
    return Store!R(range);
}


/**
return to the range separated by n elements as array.

Authors: Kazuki Komatsu(k3_kaimu)
*/
auto splitN(R)(R range, size_t n)
{
    //return SplitN!(R)(range, n);
  //static if(isForwardRange!(Unqual!R))
    //return std.range.chunks(range, n);
  //else
    return chunksEx(range, n);
}


/**
phobos extension std.range.chunks
*/
template chunksEx(Range)
if(isInputRange!Range)
{
    alias E = Unqual!(ElementType!Range);

    ChunksEx chunksEx(Range range, size_t n)
    {
        ChunksEx dst;

        dst._r = range;
        dst._arr = new E[n];
        dst._empty = false;

        foreach(i; 0 .. n){
            if(dst._r.empty){
                dst._empty = true;
                break;
            }

            dst._arr[i] = dst._r.front;
            dst._r.popFront();
        }

        return dst;
    }


    struct ChunksEx
    {
        E[] front() @property { return _arr; }
        const(E)[] front() const @property { return _arr; }


        void popFront()
        {
            if(_r.empty){
                _empty = true;
                return;
            }

            foreach(i; 0 .. _arr.length){
                if(_r.empty){
                    _arr = _arr[0 .. i];
                    return;
                }

                _arr[i] = _r.front;
                _r.popFront();
            }
        }


      static if(isInfinite!Range)
        enum bool empty = false;
      else
      {
        bool empty() const @property { return _empty; }
      }


      static if(isForwardRange!Range)
      {
        typeof(this) save() @property
        {
            typeof(this) dst;

            dst._r = this._r.save;
            dst._arr = this._arr.dup;
            dst._empty = this._empty;

            return dst;
        }
      }


      private:
        Range _r;
        E[] _arr;
        bool _empty;
    }

}


///
unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    int[] a = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    auto sna = splitN(a, 3);
    assert(equal(sna, [[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10]]));
    
    //assert(sna[0] == [0, 1, 2]);
    //assert(sna[1] == [3, 4, 5]);
    //assert(sna[2] == [6, 7, 8]);
    //assert(sna[3] == [9, 10]);
    
    //assert(sna.length == 4);

    //sna = sna[1 .. 4];
    //assert(equal(sna, [[3, 4, 5], [6, 7, 8], [9, 10]]));
    
    
    int[] b = a[0..9];
    auto snb = splitN(b, 3);
    assert(equal(snb, [[0, 1, 2], [3, 4, 5], [6, 7, 8]]));
    
    //assert(snb[0] == [0, 1, 2]);
    //assert(snb[1] == [3, 4, 5]);
    //assert(snb[2] == [6, 7, 8]);
    
    //assert(snb.length == 3);

    static struct RefIota{
        int* p;
        int lim;

        this(int n){lim = n; p = new int;}
        @property int front(){return *p;}
        @property bool empty(){return *p == lim;}
        void popFront(){++(*p);}
        @property RefIota save(){RefIota dst = this; dst.p = new int; *(dst.p) = *p; return dst;}
        @property size_t length(){return lim - *p;}
        @property RefIota opSlice(size_t a, size_t b){auto dst = save; *(dst.p) += cast(uint)a; dst.lim = *(dst.p) + cast(uint)(b - a); return dst;}
    }

    auto r = RefIota(9);
    auto snr = splitN(r, 3);
    auto check = [[0, 1, 2], [3, 4, 5], [6, 7, 8]];

    auto snrs = snr.save;
    
    foreach(i, v; check){
        assert(!snrs.empty);
        assert(equal(snrs.front, v));
        snrs.popFront();
    }

    //snrs = snr.save;
    //foreach(i, v; check)
        //assert(equal(snrs[i], v));
}



/**
return to the range separated by pred.

Authors: Kazuki Komatsu(k3_kaimu)
*/
auto splitBy(alias fun, R)(R range)
if(isForwardRange!R && is(typeof(unaryFun!fun(range.front))))
{
    static struct Result()
    {
        bool empty() @property
        {
            return _range.empty;
        }


        @property
        auto front()
        {
            return _range.save.take(_n+1);
        }


        void popFront()
        {
            _range.popFrontN(_n+1);
            _n = _range.save.countUntil!fun();
            if(_n < 0)
                _n = ptrdiff_t.max - 1;
        }


        auto save() @property
        {
            auto dst = this;
            dst._range = dst._range.save;
            return dst;
        }


      private:
        R _range;
        ptrdiff_t _n;
    }

    auto dst = Result!()(range, -1);
    dst.popFront();
    return dst;
}

///
unittest{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    int[] a = [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
    auto sna = splitBy!"(a+1)%3 == 0"(a);
    assert(equal(sna, [[0, 1, 2], [3, 4, 5], [6, 7, 8], [9, 10]]));
    
    
    int[] b = a[0 .. 9];
    auto snb = splitBy!"(a+1)%3 == 0"(b);
    assert(equal(snb, [[0, 1, 2], [3, 4, 5], [6, 7, 8]]));


    int[] c = [];
    auto snc = splitBy!"false"(c);
    assert(snc.empty);

    auto snd = splitBy!"true"(c);
    assert(snc.empty);

    auto sne = splitBy!"true"(a);
    assert(equal(sne, [[0], [1], [2], [3], [4], [5], [6], [7], [8], [9], [10]]));

    auto snf = splitBy!"false"(a);
    assert(equal(snf, [a]));
}


/**
return the range with the element that receives the range in which the elements are ubyte value,
was converted to the type T as a binary

Example:
------
int[] a = [1, 2, 3, 4, 5];
ubyte[] ubs = cast(ubyte[])a;

assert(equal(interpret!int(ubs), a));



struct S
{
    ubyte a;
    ushort b;
}

S[] sb = [S(1, 1), S(2, 2), S(3, 3)];
ubyte[] ubsb = cast(ubyte[])sb;

assert(equal(interpret!S(ubsb), sb));
------

Authors: Kazuki Komatsu(k3_kaimu)
*/
template interpret(T, R)
if(isInputRange!R && is(ElementType!(Unqual!R) == ubyte))
{
    ///ditto
    auto interpret(R range)
    {
        return map!convFun(splitN(range, T.sizeof));
    }
    
    T convFun(ubyte[] bin) pure @safe
    {
        return (cast(T[])bin)[0];
    }
}

unittest
{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    int[] a = [1, 2, 3, 4, 5];
    ubyte[] ubs = cast(ubyte[])a;
    
    assert(equal(interpret!int(ubs), a));
    
    struct S
    {
        ubyte a;
        ushort b;
    }
    
    S[] sb = [S(1, 1), S(2, 2), S(3, 3)];
    ubyte[] ubsb = cast(ubyte[])sb;
    
    assert(equal(interpret!S(ubsb), sb));
}


/**
memozied
*/
auto memoized(bool forceSave = true, Range)(Range range, size_t size = 4096)
if(isInputRange!Range)
{
  static if(isArray!Range)
    return range;
  else
  {
    alias R = Unqual!Range;
    alias E = ElementType!R;
    alias Handle = size_t;

    static struct Memo()
    {
      private:
        R _range;

      static if(hasLvalueElements!R)
        E*[] _buf;
      else
        E[] _buf;

        size_t[] _posOfHandle;


        auto ref minIdx() @property pure nothrow @safe inout
        {
            return _posOfHandle[0];
        }


        auto ref endIdx() @property pure nothrow @safe inout
        {
            return _posOfHandle[1];
        }


        Handle getNewHandle(size_t pos) pure nothrow @safe
        in{
            assert(pos >= this.minIdx);
            assert(pos <= this.endIdx);
        }
        body{
            foreach(i, ref e; _posOfHandle[2 .. $])
                if(!e){
                    e = pos;
                    return i + 2;
                }

            _posOfHandle ~= pos;
            return _posOfHandle.length - 1;
        }


        //ハンドルhを受け取って、それの子供となるものを返します。
        Handle getNewChild(Handle h) pure nothrow @safe
        in{
            assert(h >= 2);
            assert(h < _posOfHandle.length);
        }
        body{
            return getNewHandle(_posOfHandle[h]);
        }


        void reSlicing() pure nothrow @safe
        {
            size_t minIdx = this.minIdx/*, maxIdx = this.endIdx - 1*/;
            foreach(e; _posOfHandle[2 .. $]){
                if(e)
                    minIdx = min(e, minIdx);

                //maxIdx = max(e, maxIdx);
            }

            this.minIdx = minIdx;
            //this.endIdx = maxIdx + 1;
        }


        ///ハンドルhを受け取り、そのハンドルを無効化します。
        void releaseHandle(Handle h) pure @safe
        in{
            assert(h >= 2);
            assert(h < _posOfHandle.length);
        }
        body{
            immutable cpos = _posOfHandle[h];
            _posOfHandle[h] = 0;

            if(cpos == this.minIdx)
                reSlicing();
        }


        auto ref getValue(Handle h) pure @safe nothrow inout
        in{
            assert(h >= 2);
            assert(h < _posOfHandle.length);
        }
        body{
          static if(hasLvalueElements!R)
            return *(_buf[_posOfHandle[h] % _buf.length]);
          else
            return cast(E)_buf[_posOfHandle[h] % _buf.length]; // to rvalue
        }


        bool isEmpty(Handle h)
        in{
            assert(h >= 2);
            assert(h < _posOfHandle.length);
        }
        body{
            return _posOfHandle[h] >= this.endIdx && _range.empty;
        }


        size_t popFrontN(Handle h, size_t n)
        in{
            assert(h >= 2);
            assert(h < _posOfHandle.length);
        }
        body{
            immutable beforePos = _posOfHandle[h];

            if(!n)
                return 0;
            else if((_posOfHandle[h] + n) < this.endIdx)
            {
                immutable cpos = _posOfHandle[h];
                _posOfHandle[h] += n;

                if(cpos == this.minIdx)
                    reSlicing();

                return n;
            }
            else
            {
                immutable remN = this.endIdx - _posOfHandle[h] - 1;
                size_t ret = this.popFrontN(h, remN);
                assert(_posOfHandle[h] == this.endIdx - 1);

                n -= remN;
                _posOfHandle[h] += n;
                while(_posOfHandle[h] - this.minIdx >= _buf.length){
                    _buf.length <<= 1;
                    _buf[$>>1 .. $][] = _buf[0 .. $>>1];
                }

                while(this.endIdx <= _posOfHandle[h] && !_range.empty){
                    _buf[this.endIdx % _buf.length] = _range.front;
                    _range.popFront();
                    ++ret;
                    ++this.endIdx;
                }

                if(_posOfHandle[h] > this.endIdx)
                    _posOfHandle[h] = this.endIdx;

                return ret;
            }
        }


      static if(hasLength!R)
        size_t length(Handle h)
        {
            return _range.length + (this.endIdx - _posOfHandle[h]);
        }
    }

    static struct Result()
    {
        this(this)
        {
            _h = _memo.getNewChild(_h);
        }


        ~this()
        {
            if(_h && _memo)
                _memo.releaseHandle(_h);
        }


      static if(forceSave)
        void opAssign()(auto ref typeof(this) rhs)
        {
            this._memo = rhs._memo;
            this._h = this._memo.getNewChild(rhs._h);
        }


        auto ref front() @property inout
        {
            return _memo.getValue(_h);
        }


        void popFront()
        {
            popFrontN(1);
        }


        size_t popFrontN(size_t n)
        {
            return _memo.popFrontN(_h, n);
        }

      static if(isInfinite!R)
        enum empty = false;
      else
        bool empty() @property
        {
            return _memo.isEmpty(_h);
        }



        auto save() @property
        {
          static if(forceSave)
            return this;
          else
            return RefCounted!(typeof(this))(this);
        }


        auto ref opIndex(size_t idx)
        {
            auto t = this;
            t.popFrontN(idx);
            return t.front;
        }


        auto opSlice()
        {
            return this.save;
        }


        auto opSlice(size_t n, size_t m)
        in{
            assert(n <= m);
        }
        body{
            auto t = this.save;
            t.popFrontExactly(n);
            return t.takeExactly(m - n);
        }


      static if(hasLength!R)
      {
        size_t length()
        {
            return _memo.length(_h);
        }


        alias opDollar = length;
      }

      private:
        Memo!()* _memo;
        Handle _h;
    }

    Result!() dst;

    //dst._memo = new Memo!()(range);
    dst._memo = new Memo!();
    dst._memo._range = range;
    dst._memo._buf.length = size;
    if(!dst._memo._range.empty){
        dst._memo._buf[1] = dst._memo._range.front;
        dst._memo._range.popFront();
        dst._memo._posOfHandle = [1, 2, 1];
        dst._h = 2;
    }else{
        dst._memo._posOfHandle = [1, 1, 1];
        dst._h = 2;
    }

    return dst.save;
  }
}


/**
return a forward-range from a input-range.

Example:
---
struct IRange{
    size_t* _f;
    size_t _l;

    this(size_t limit){
        _f = new size_t;
        (*_f) = 0;
        _l = limit;
    }

    @property
    size_t front(){return *_f;}

    @property
    bool empty(){return (_l <= *_f);}

    void popFront(){*_f += 1;}
}


auto r = IRange(5);
auto sr = toForwardRange(r);
assert(equal(sr.save, [0, 1, 2, 3, 4]));
assert(equal(sr, [0, 1, 2, 3, 4]));
---

Authors: Kazuki Komatsu(k3_kaimu)
*/
R toForwardRange(R)(R r)
if(isForwardRange!(Unqual!R))
{
    return r;
}


auto toForwardRange(R)(R r)
if(!isForwardRange!(Unqual!R) && isInputRange!(Unqual!R))
{
    return r.memoized;
}

unittest{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    static struct IRange{
        size_t* _f;
        size_t _l;

        this(size_t limit){
            _f = new size_t;
            *_f = 0;
            _l = limit;
        }

        @property
        size_t front(){return *_f;}

        @property
        bool empty(){return (_l <= *_f);}

        void popFront(){*_f += 1;}

        size_t length() @property { return _l - *_f; }
    }


    auto r = IRange(5);
    auto sr = memoized(r);
    static assert(isInputRange!(typeof(sr)));
    static assert(isForwardRange!(typeof(sr)));
    assert(equal(sr.save, [0, 1, 2, 3, 4]));
    assert(equal(sr, [0, 1, 2, 3, 4]));
    assert(sr.length == 5);

    auto r2 = IRange(4096);
    auto sr1 = memoized(r2);

    auto sr2 = sr1.save;//save
    auto sr3 = sr2;     //this(this)

    typeof(sr3) sr4;
    sr4 = sr3;          //opAssing

    auto arr = array(sr1.save);

    assert(equal(sr1, arr));
    assert(equal(sr2, arr));
    assert(equal(sr3, arr));
    assert(equal(sr4, arr));

    auto r3 = IRange(4096);
    auto r31 = memoized(r3, 1024);
    auto r32 = r31.save;
    auto r33 = r32;
    typeof(r33) r34;
    r34 = r33;

    assert(r31.popFrontN(2048) == 2048);
    assert(equal(r32, arr));
    assert(equal(r33, arr));
    assert(equal(r34, arr));

    assert(r31.popFrontN(1024) == 1024);
    assert(equal(r32, arr));
    assert(equal(r33, arr));
    assert(equal(r34, arr));

    assert(r32.popFrontN(2048 + 1024) == 3072);
    assert(r33.popFrontN(2048 + 1024) == 3072);
    assert(r34.popFrontN(2048 + 1024) == 3072);
    assert(equal(r31, r32));
    assert(equal(r32, r33));
    assert(equal(r33, r34));

    assert(r31.popFrontN(10) == 10);
    assert(r32.popFrontN(10) == 10);
    assert(r33.popFrontN(10) == 10);
    assert(r34.popFrontN(10) == 10);
    assert(equal(r31, r32));
    assert(equal(r32, r33));
    assert(equal(r33, r34));

    assert(r31.popFrontN(1024) == 1023-10);     // 1023 : 1024 - 1(first-0)
    assert(r32.popFrontN(1024) == 1023-10);
    assert(r33.popFrontN(1024) == 1023-10);
    assert(r34.popFrontN(1024) == 1023-10);
    assert(equal(r31, r32));
    assert(equal(r32, r33));
    assert(equal(r33, r34));

    r31 = r32;
    assert(equal(r31, r32));

    auto r4 = IRange(0);
    assert(r4.empty);

    auto r41 = memoized(r4);
    auto r42 = r41;
    assert(r41.empty);
    assert(r42.empty);

    auto r5 = IRange(1024).memoized();
    assert(equal(r5[0 .. 5], r5[0 .. 5]));
    assert(r5[0 .. 5].length == 5);
    assert(equal(r5[10 .. 1024], r5[10 .. 1024]));
    assert(r5[10 .. 1024].length == 1024 - 10);

    assert(equal(r5[512 .. 1024], r5[$/2 .. $]));
    assert(r5[0 .. 0].empty);
    assert(r5[$ .. $].empty);
}



/**
"yield" as in Python, Ruby or C#.

Example:
---
auto r1 = {
    void func(Yield!int yield){
        foreach(i; 0 .. 100)
            yield = i;
    }
    
    return yieldRange(&func);
}();

assert(equal(r1, iota(100)));


auto r2 = {
    void func(Yield!int yield){
        foreach(i; 0 .. 100)
            if(i&1)
                yield = i;
    }
    
    return yieldRange(&func);
}();

assert(equal(r2, filter!"a&1"(iota(100))));

auto r3 = {
    int sum;

    void func(Yield!int yield){
        while(1){
            sum += yield.value * yield.next;
        }
    }

    return tuple(yieldRange(&func), () => sum);
}();

put(r3[0], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
assert(r3[1]() == (0*1 + 1*2 + 2*3 + 3*4 + 4*5 + 5*6 + 6*7 + 7*8 + 8*9 + 9*10));
---

Authors: Kazuki Komatsu(k3_kaimu)
*/
class Yield(T) : Fiber{
private:
    T _value;


public:
    this(void delegate(typeof(this)) dlg){
        super( (){dlg(this);} );
    }


    this(void function(typeof(this)) fn){
        super( (){fn(this);} );
    }


    void opAssign(T v){
        _value = v;
        this.yield();
    }


    @property
    ref T next(){
        this.yield();
        return _value;
    }


    @property
    ref T value() pure @safe nothrow{
        return _value;
    }
}


///ditto
template yieldRange(T){
    import core.thread : Fiber;

    ///ditto
    YieldRange yieldRange(void delegate(Yield!T) dlg){
        return YieldRange(dlg);
    }


    ///ditto
    YieldRange yieldRange(void function(Yield!T) dlg){
        return YieldRange(dlg);
    }


    struct YieldRange{
    private:
        Yield!T _yield;

    public:
        this(void delegate(Yield!T) dlg){
            _yield = new Yield!T(dlg);
            popFront();
        }


        this(void function(Yield!T) dlg){
            _yield = new Yield!T(dlg);
            popFront();
        }


        @property
        ref T front(){
            return _yield._value;
        }


        void popFront(){
            _yield.call();
        }


        @property
        bool empty(){
            return (_yield.state == Fiber.State.TERM);
        }
    }
}


unittest{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}

    auto r1 = {
        void func(Yield!int yield){
            foreach(i; 0 .. 100)
                yield = i;
        }
        
        return yieldRange(&func);
    }();

    assert(equal(r1, iota(100)));


    auto r2 = {
        void func(Yield!int yield){
            foreach(i; 0 .. 100)
                if(i&1)
                    yield = i;
        }
        
        return yieldRange(&func);
    }();

    assert(equal(r2, filter!"a&1"(iota(100))));

    auto r3 = {
        int sum;

        void func(Yield!int yield){
            while(1){
                sum += yield.value * yield.next;
            }
        }

        return tuple(yieldRange(&func), () => sum);
    }();

    put(r3[0], [1, 2, 3, 4, 5, 6, 7, 8, 9, 10]);
    assert(r3[1]() == (0*1 + 1*2 + 2*3 + 3*4 + 4*5 + 5*6 + 6*7 + 7*8 + 8*9 + 9*10));
}


mixin template InfiniteDollarToken(IndexType){
    struct DollarToken{
        IndexType value;

        DollarToken opBinary(string op, T)(T v) pure nothrow @safe const if(is(typeof({IndexType a; a += T.init;}))){
            static if(op == "-")
                return DollarToken(value + v);
            else static if(op == "+")
                return DollarToken(value - v);
            else static if(op == "*" || op == "/")
                return DollarToken(mixin("value " ~ op ~ " v"));
            else
                static assert(0, "InifiniteDollarToken does not support the operator '" ~ op ~ "'");
        }


        auto opBinaryRight(string op, T)(T v) pure nothrow @safe const if(is(typeof({IndexType a; a += T.init;}))){
            static if(op == "-")
                return DollarToken(value + v);
            else static if(op == "+")
                return DollarToken(value - v);
            else static if(op == "*")
                return DollarToken(value * v);
            else static if(op == "-")
                return cast(IndexType)0;
            else
                static assert(0, "InifiniteDollarToken does not support the operator '" ~ op ~ "'");
        }


        IndexType opBinary(string s = "-")(DollarToken dollar) pure nothrow @safe const if(is(typeof({IndexType a; a += T.init;}))){
            return dollar.value - value;
        }
    }
}


///std.range.iota-version Infinite and Bidirectional Range
template iotaInfinite(T)
if(checkFunctionAttribute!(FunctionAttribute.pure_ | FunctionAttribute.nothrow_ | FunctionAttribute.safe,
    "(){a += a; a -= a; a = a; a = a - a; return a + b * a;}", T, size_t)){
    IotaInfinite iotaInfinite(T start, T diff = 1) pure nothrow @safe{
        return IotaInfinite(start, diff);
    }

    
    struct IotaInfinite{
    private:
        T _front;
        T _back;

        T _diff;

        mixin InfiniteDollarToken!(long);

    public:
        enum empty = false;

        this(T s, T d) pure nothrow @safe{
            _front = s;
            _back = s - d;
            _diff = d;
        }

        this(T s, T e, T d) pure nothrow @safe{
            _front = s;
            _back = e;
            _diff = d;
        }
        
        void popFront() pure nothrow @safe{
            _front += _diff;
        }


        void popBack() pure nothrow @safe{
            _back -= _diff;
        }
        
        T front() pure nothrow @safe const @property{
            return _front;
        }

        T back() pure nothrow @safe const @property{
            return _back;
        }

        T opIndex(size_t i) pure nothrow @safe const{
            return cast(T)(_front + i * _diff);
        }

        T opIndex(DollarToken dollar) pure nothrow @safe const 
        in{
            assert(dollar.value >= 0);
        }
        body{
            return cast(T)(_back - (dollar.value -1) * _diff);
        }

        static DollarToken opDollar() pure nothrow @safe{return DollarToken.init;}
        
        @property
        typeof(this) save() pure nothrow @safe const{
            return this;
        }

        typeof(this) opSlice() pure nothrow @safe const{
            return this;
        }

        auto opSlice(size_t i, size_t j) const {
            return iota(cast(T)(_front + i * _diff), cast(T)(_front + j * _diff), _diff);
        }

        auto opSlice(size_t i, DollarToken dollar) pure nothrow @safe const 
        in{
            assert(dollar.value >= 0);
        }
        body{
            return typeof(this)(cast(T)(_front + i * _diff), cast(T)(_back + dollar.value * _diff), _diff);
        }


        auto opSlice(DollarToken first, DollarToken second) const 
        in{
            assert(first.value >= 0);
            assert(second.value >= 0);
        }
        body{
            return iota(cast(T)(_back - (first.value -1) * _diff), cast(T)(_back - (second.value - 1) * _diff), _diff);
        }
    }
}


unittest{
    debug scope(failure) writefln("unittest Failure :%s(%s)", __FILE__, __LINE__);
    debug scope(success) {writefln("Unittest Success :%s(%s)", __FILE__, __LINE__); stdout.flush();}
    
    auto inf = iotaInfinite(12);
    assert(equal(take(inf, 10), [12,13,14,15,16,17,18,19,20,21]));
    assert(equal(take(inf.retro, 10), [11,10,9,8,7,6,5,4,3, 2]));
    assert(equal(inf[0 .. 5], [12, 13, 14, 15, 16]));
    assert(equal(take(inf[1 .. $], 5), [13,14,15,16,17]));
    assert(equal(take(inf[$-5 .. $], 5), [7, 8, 9, 10, 11]));
    assert(inf[0] == 12);
    assert(inf[1] == 13);
    assert(inf[2] == 14);
    assert(inf[$-1] == 11);
    assert(inf[$-2] == 10);
    assert(inf[$ .. $].empty);
    assert(equal(inf[$ - $ + $ - 100 .. $ - ($ - ($ - 5))], inf[$ - 100 .. $ - 5]));
    assert(inf[0 .. 0].empty);

    inf = iotaInfinite(10, -1);
    assert(equal(take(inf, 10), [10,9,8,7,6,5,4,3,2,1]));
}
// Written in the D programming language.

/**
License:   <a href="http://www.boost.org/LICENSE_1_0.txt">Boost License 1.0</a>.
Authors:   Komatsu Kazuki(k3_kaimu)
*/

module dranges.rational;

import std.algorithm, std.array, std.bigint, std.format, std.traits;
import dranges.traits;

debug import std.stdio;


/*
if T is like int, isLikeInt!T is true. Where "like int" type has operators same of int.

Example:
---
static assert(!isLikeInt!(byte));
static assert(!isLikeInt!(short));
static assert(isLikeInt!(int));
static assert(isLikeInt!(long));
static assert(!isLikeInt!(ubyte));
static assert(!isLikeInt!(ushort));
static assert(isLikeInt!(uint));
static assert(isLikeInt!(ulong));

static assert(isLikeInt!(BigInt));
---
*/
private
template isLikeInt(T){
    enum bool isLikeInt = is(typeof(
        {
            T a = 1;
            a = 0;
            a = a;
            
            ++a;
            --a;
            a++;
            a--;
            a = -a;
            a = +a;
            
            a += a;
            a -= a;
            a *= a;
            a /= a;
            a %= a;
            //a ^^= a;

            a += 1;
            a -= 1;
            a *= 1;
            a /= 1;
            a %= 1;
            a ^^= 1;
            
            a = a + a;
            a = a - a;
            a = a * a;
            a = a / a;
            a = a % a;
            //a = a ^^ a;

            a = a + 1;
            a = a - 1;
            a = a * 1;
            a = a / 1;
            a = a % 1;
            a = a ^^ 1;

            bool b = a < 0;
            b = a == 0;
        }));
}
unittest{
    static assert(!isLikeInt!(byte));
    static assert(!isLikeInt!(short));
    static assert(isLikeInt!(int));
    static assert(isLikeInt!(long));
    static assert(!isLikeInt!(ubyte));
    static assert(!isLikeInt!(ushort));
    static assert(isLikeInt!(uint));
    static assert(isLikeInt!(ulong));

    static assert(isLikeInt!(BigInt));
}


private
template isLikeBuiltInInt(T){
    enum checkCode = q{
        (){
            alias typeof(a) T;

            T b = 1;
            b = 0;
            b = b;

            ++b;
            --b;
            b++;
            b--;
            b = -b;
            b = +b;

            b += b;
            b -= b;
            b *= b;
            b /= b;
            b %= b;
            //b ^^= b;

            b += 1;
            b -= 1;
            b *= 1;
            b /= 1;
            b %= 1;
            b ^^= 1;

            b = b + b;
            b = b - b;
            b = b * b;
            b = b / b;
            b = b % b;
            //b = b ^^ b;

            b = b + 1;
            b = b - 1;
            b = b * 1;
            b = b / 1;
            b = b % 1;
            b = b ^^ 1;

            bool c = b < 0;
            c = b == 0;
        }()};
    
    enum isLikeBuiltInInt = dranges.traits.isPure!(checkCode, T) && dranges.traits.isNothrow!(checkCode, T) && dranges.traits.isSafe!(checkCode, T);
}
unittest{
    static assert(isLikeBuiltInInt!int);
    static assert(isLikeBuiltInInt!long);
}



private
auto gcd(T, U)(T a, U b){
    alias C = Unqual!(CommonType!(T, U));

    C _a = a < 0 ? a * -1 : a,
      _b = b < 0 ? b * -1 : b;

    while(_a != 0 && _b != 0){
        if(_a > _b)
            _a %= _b;
        else
            _b %= _a;
    }

    if(_a == 0)
        return _b;
    else
        return _a;
}



private
CommonType!(T, U) lcm(T, U)(T a, U b){
    return a / gcd(a, b) * b;
}


/**
This is the type that you can calculate fraction.
$(B Rational!T) has two integral $(B T) values.

Example:
---
auto r = rational(10, 2);       // If you called rational(n, d), value is reduced.
assert(r.num == 5);             // 10 / 2 => 5 / 1
assert(r.den == 1);

assert(r == rational(5));       // rational(5) == rational(5, 1)

assert(r == 5.per(1));          // UFCS : n.per(d) == n.rational(d) == rational(n, d)

r *= -1.per(5);
assert(r.num == -1);            // If rational value is negative, numerator is always negative.
assert(r.den == 1);             // But denominator is always positive.
assert(r == rational(1, 1));    // (5 / 1) * (1 / 5) == (1 / 1)
assert(r == 1);                 // Can check equality to T by "==" operator.
assert(r > 2);                  // Also comparison operator.

r1 = 2.per(5) + 3;              // You can use Rational!T like T.

import std.bigint;
Rational!BigInt rb = 10.per(33);// You can use BigInt as T.
rb ^^= -10;
assert(rb == Rational!BigInt(BigInt(33)^^10, BigInt(10)^^10));
---

If $(B T) can be operated in $(B pure nothrow @safe function),
$(B Rational!T) can be too.

Example:
-------------------------------------------------------
void foo() pure nothrow @safe
{
    auto r = rational(1, 3);    //int is pure nothrow @safe type
    r += 3.per(4);
    ...
}
-------------------------------------------------------

You can use $(B "%(...%)") format when formatted write.
Where inner format $(B "...") can be $(B T)'s format, first one is numerator's format, second is denominator's format.

Example:
---
import std.format;

void main(){
    auto writer = appender!string;

    formattedWrite(writer, "%(%04d / %04d%)", rational(10, 33));
    assert(writer.data == "0010 / 0033");

    writer = appender!string;
    formattedWrite(writer, "%(den : %2$s , num : %1$s%)", rational(10, 33));
    assert(writer.data == "den : 33 , num : 10");

    writer = appender!string;
    formattedWrite(writer, "%04d", rational(10, 30));
    assert(writer.data == "0010/0030");
}
---
*/
struct Rational(T)if(isLikeBuiltInInt!T){
private:
    T _num;             //分子
    T _den = 1;         //分母

    /*
    invariant() pure @safe const{
        assert(_den != 0);
    }
    */


    void reduce() pure nothrow @safe {
        debug "reduce:\n Input: _num : %s, _den : %s".writefln(_num, _den);
        if(_num == 0){
            if(_den < 0)
                _den = -1;
            else
                _den = 1;
        }else{
            auto _gcd = gcd(_num, _den);
            _num /= _gcd;
            _den /= _gcd;
            debug "......: _num : %s, _den : %s".writefln(_num, _den);
        }

        if(_den < 0){
            _num = -_num;
            _den = -_den;
        }
        debug "Output: _num : %s, _den : %s".writefln(_num, _den);
    }

    
public:

  version(none){
    static typeof(this) init() @property pure nothrow @safe {
        static if(is(typeof({typeof(this) r = typeof(this)(0, 1);})))
            typeof(this) r = typeof(this)(0, 1);
        else{
            typeof(this) r;
            ++r._den;
        }
        return r;
    }
  }


    ///ditto
    this(U)(U n) pure nothrow @safe{
        _num = n;
        _den = 1;
    }


    ///ditto
    this(U, V)(U n, V d, bool nonReduce = false) pure nothrow @safe if(isAssignable!(T, U) && isAssignable!(T, V)) {
        _num = n;
        _den = d;
        debug writefln("%s / %s", _num, _den);
        if(!nonReduce) reduce();
    }


    /// numerator
    @property
    inout(T) num()() pure nothrow @safe inout {return _num;}

    /// ditto
    @property
    void num(U)(U u) pure nothrow @safe if(isAssignable!(T, U)) {
        _num =  u;
        reduce();
    }

    /// denominator
    @property
    inout(T) den()() pure nothrow @safe inout {return _den;}

    /// ditto
    @property
    void den(U)(U u) pure nothrow @safe if(isAssignable!(T, U))
    in{
        assert(u != 0);
    }body{
        _den = u;
        reduce();
    }

    
    /// return reciprocal number
    @property
    inout(typeof(this)) reciprocal() pure nothrow @safe inout {return _num < 0 ? typeof(this)(-_den, -_num, false) : typeof(this)(_den , _num, false);}


    /// operator
    void opAssign(U)(const U v) pure nothrow @safe if(!isRationalType!U && isAssignable!(T, U)){
        _den = 1;
        _num = v;
    }


    /// ditto
    void opAssign(U)(auto ref const Rational!U r) pure nothrow @safe if(isAssignable!(T, U)) {
        _den = r._den;
        _num = r._num;
    }


    /// ditto
    inout(typeof(this)) opUnary(string op)() pure nothrow @safe inout if(!find(["-", "+"], op).empty)
    {
        static if(op == "-")
            return rational(-_num, _den);
        else static if(op == "+")
            return rational(_num, _den);
    }


    /// ditto
    typeof(this) opUnary(string op)() pure nothrow @safe if(!find(["++", "--"], op).empty)
    {
        static if(op == "++")
            _num += _den;
        else static if(op == "--")
            _num -= _den;

        return this;
    }


    ///ditto
    bool opCast(U : bool)() pure nothrow @safe const {
        return _num != 0;
    }


    ///ditto
    U opCast(U : T)() pure nothrow @safe const {
        return _num / _den;
    }


    /// ditto
    U opCast(U)() pure nothrow @safe const if(isRationalType!U && is(typeof({auto e = U(_num, _den);}))){
        return U(_num, _den, true);
    }


    /// ditto
    U opCast(U)() pure nothrow @safe const if(isRationalType!U && !is(typeof({auto e = U(_num, _den);})) && is(typeof({auto e = cast(typeof(U.init._num))_num;})))
    {
        alias E = typeof(U.init._num);
        return U(cast(E)_num, cast(E)_den, true);
    }


    /// ditto
    auto opBinary(string op, U)(auto ref const Rational!U r) pure nothrow @safe const if(!find(["+", "-", "*", "/", "%"], op).empty)
    {
       static if(op == "+"){
            auto gcd1 = gcd(_den, r._den);
            return rational(_num * (r._den / gcd1) + r._num * (_den / gcd1), _den / gcd1 * r._den);
        }
        else static if(op == "-"){
            auto gcd1 = gcd(_den, r._den);
            return rational(_num * (r._den / gcd1) - r._num * (_den / gcd1), _den / gcd1 * r._den);
        }
        else static if(op == "*"){
            auto gcd1 = gcd(_num, r._den);
            auto gcd2 = gcd(r._num, _den);
            return rational((_num/gcd1) * (r._num / gcd2), (_den/gcd2) * (r._den / gcd1), true);
        }
        else static if(op == "/"){
            auto gcd1 = gcd(_num, r._num);
            auto gcd2 = gcd(r._den, _den);
            if(r._num < 0)
                gcd1 = -gcd1;
            return rational((_num/gcd1) * (r._den / gcd2), (_den/gcd2) * (r._num / gcd1), true);
        }
        else static if(op == "%"){
            auto gcd1 = gcd(_den, r._den);
            return rational((_num * (r._den / gcd1)) % (r._num * (_den / gcd1)), _den / gcd1 * r._den);
        }
    }


    /// ditto
    auto opBinary(string op, U)(const U v) pure nothrow @safe const if(!isRationalType!U && !find(["+", "-", "*", "/", "%", "^^"], op).empty)
    {
        static if(op == "+")
            return rational(_num + _den * v, _den);
        else static if(op == "-")
            return rational(_num - _den * v, _den);
        else static if(op == "*")
            return rational(_num * v, _den);
        else static if(op == "/")
            return rational(_num, _den * v);
        else static if(op == "%")
            return rational(_num % (v * _den), _den);
        else static if(op == "^^"){
            if(v >= 0)
                return rational(_num ^^ v, _den ^^ v);
            else
                return rational(_den ^^ (-v), _num ^^ (-v));
        }
    }


    /// ditto
    auto opBinaryRight(string op, U)(const U v) pure nothrow @safe const if(!isRationalType!U && !find(["+", "-", "*", "/", "%"], op).empty)
    {
        static if(op == "+")
            return rational(_num + _den * v, _den);
        else static if(op == "-")
            return rational(_den * v - num, _den);
        else static if(op == "*")
            return rational(_num * v, _den);
        else static if(op == "/")
            return rational(v * _den, _num);
        else static if(op == "%")
            return rational((v * _den) % _num, _den);
    }


    /// ditto
    void opOpAssign(string op, U)(auto ref const Rational!U r) pure nothrow @safe if(!find(["+", "-", "*", "/", "%"], op).empty)
    in{
        static if(op == "/")
            assert(r._num != 0);
    }
    body{
        static if(op == "+"){
            auto gcd1 = gcd(_den, r._den);
            _num = _num * (r._den / gcd1) + r._num * (_den / gcd1);
            _den = _den / gcd1 * r._den;
            reduce();
        }
        else static if(op == "-"){
            auto gcd1 = gcd(_den, r._den);
            _num = _num * (r._den / gcd1) - r._num * (_den / gcd1);
            _den = _den / gcd1 * r._den;
            reduce();
        }
        else static if(op == "*"){
            auto gcd1 = gcd(_num, r._den);
            auto gcd2 = gcd(r._num, _den);
            _num = (_num / gcd1) * (r._num / gcd2);
            _den = (_den / gcd2) * (r._den / gcd1);
        }
        else static if(op == "/"){
            auto gcd1 = gcd(_num, r._num);
            auto gcd2 = gcd(r._den, _den);

            if(r._num >= 0){
                _num = (_num / gcd1) * (r._den / gcd2);
                _den = (_den / gcd2) * (r._num / gcd1);
            }else{
                _num = -(_num / gcd1) * (r._den / gcd2);
                _den = -(_den / gcd2) * (r._num / gcd1);
            }
        }
        else static if(op == "%"){
            auto gcd1 = gcd(_den, r._den);
            _num = (_num * (r._den / gcd1)) % (r._num * (_den / gcd1));
            _den = _den / gcd1 * r._den;
            reduce();
        }
    }


    /// ditto
    void opOpAssign(string op, U)(const U v) pure nothrow @safe if(!isRationalType!U && !find(["+", "-", "*", "/", "%", "^^"], op).empty)
    in{
        static if(op == "^^")
            assert(!(v < 0 && _num == 0));
    }
    body{
        static if(op == "+"){
            _num += _den * v;
        }else static if(op == "-"){
            _num -= _den * v;
        }else static if(op == "*"){
            _num *= v;
            reduce();
        }else static if(op == "/"){
            _den *= v;
            reduce();
        }else static if(op == "%"){
            _num %= _den * v;
            reduce();
        }else static if(op == "^^"){
            if(v >= 0){
                _num ^^= v;
                _den ^^= v;
            }else{
                if(_num >= 0){
                    _num = _den ^^ (-v);
                    _den = _num ^^ (-v);
                }else{
                    auto tmp = -_num;
                    _num = (-_den) ^^ (-v);
                    _den = (tmp) ^^ (-v);
                }
            }
        }
    }


    /// ditto
    auto opCmp(U)(auto ref const U r) pure nothrow @safe const if(!isRationalType!U){
        return _num - r * _den;
    }


    /// ditto
    auto opCmp(U)(auto ref Rational!U r) pure nothrow @safe const {
        auto _gcd = gcd(_den, r._den);
        return (_num * (r._den / _gcd)) - (r._num * (_den / _gcd));
    }


    /// ditto
    bool opEquals(U)(auto ref const U v) pure nothrow @safe const if(!isRationalType!U){
        return _den == 1 && _num == v;
    }


    /// ditto
    bool opEquals(U)(auto ref const Rational!U r) pure nothrow @safe const {
        return (_num == r._num) && (_den == r._den);
    }


    /// ditto
    void toString(scope void delegate(const(char)[]) sink, FormatSpec!char fmt) const {
        if(fmt.nested.length != 0){
            formattedWrite(sink, fmt.nested, _num, _den);
        }else{
            formatValue(sink, _num, fmt);
            sink("/");
            formatValue(sink, _den, fmt);
        }
    }
}


/// ditto
struct Rational(T)if(isLikeInt!T && !isLikeBuiltInInt!T){
private:
    T _num;             //分子
    T _den = 1;         //分母

    /*
    invariant() pure @safe const{
        assert(_den != 0);
    }
    */


    void reduce() {
        debug "reduce:\n Input: _num : %s, _den : %s".writefln(_num, _den);
        if(_num == 0){
            if(_den < 0)
                _den = -1;
            else
                _den = 1;
        }else{
            auto _gcd = gcd(_num, _den);
            _num /= _gcd;
            _den /= _gcd;
            debug "......: _num : %s, _den : %s".writefln(_num, _den);
        }

        if(_den < 0){
            _num = -_num;
            _den = -_den;
        }
        debug "Output: _num : %s, _den : %s".writefln(_num, _den);
    }

    
public:

  version(none){
    static typeof(this) init() @property {
        static if(is(typeof({typeof(this) r = typeof(this)(0, 1);})))
            typeof(this) r = typeof(this)(0, 1);
        else{
            typeof(this) r;
            ++r._den;
        }
        return r;
    }
  }


    /// n / 1 の形
    this(U)(U n){
        _num = n;
        _den = 1;
    }


    /// n / d の形。nonReduceをtrueにすると、コンストラクタでの約分などが実行されなくなる
    this(U, V)(U n, V d, bool nonReduce = false) if(isAssignable!(T, U) && isAssignable!(T, V)) {
        _num = n;
        _den = d;
        debug writefln("%s / %s", _num, _den);
        if(!nonReduce) reduce();
    }


    /// 分子
    @property
    inout(T) num()() pure nothrow @safe inout {return _num;}

    @property
    void num(U)(U u) if(isAssignable!(T, U)) {
        _num =  u;
        reduce();
    }

    /// 分母を返す
    @property
    inout(T) den()() pure nothrow @safe inout {return _den;}

    @property
    void den(U)(U u) if(isAssignable!(T, U))
    in{
        assert(u != 0);
    }body{
        _den = u;
        reduce();
    }

    
    /// 
    @property
    typeof(this) reciprocal() {return _num < 0 ? typeof(this)(-_den, -_num, false) : typeof(this)(_den , _num, false);}


    ///op
    void opAssign(U)(U value) if(!isRationalType!U && isAssignable!(T, U)){
        _den = 1;
        _num = value;
    }

    /+
    ///ditto
    void opAssign(U)(ref const Rational!U r) if(isAssignable!(T, U)) {
        _den = r._den;
        _num = r._num;
    }
    +/


    void opAssign(U)(Rational!U r) if(isAssignable!(T, U)) {
        _den = r._den;
        _num = r._num;
    }


    typeof(this) opUnary(string op)() if(!find(["-", "+"], op).empty)
    {
        static if(op == "-")
            return rational(-_num, _den);
        else static if(op == "+")
            return rational(_num, _den);
    }


    typeof(this) opUnary(string op)() if(!find(["++", "--"], op).empty)
    {
        static if(op == "++")
            _num += _den;
        else static if(op == "--")
            _num -= _den;

        return this;
    }


    ///ditto
    bool opCast(U : bool)() const {
        return _num != 0;
    }


    ///ditto
    U opCast(U : T)() const {
        return cast()_num / cast()_den;
    }


    U opCast(U)() pure nothrow @safe const if(isRationalType!U && is(typeof({auto e = U(_num, _den);}))){
        return U(_num, _den, true);
    }


    U opCast(U)() pure nothrow @safe const if(isRationalType!U && !is(typeof({auto e = U(_num, _den);})) && is(typeof({auto e = cast(typeof(U.init._num))_num;})))
    {
        alias E = typeof(U.init._num);
        return U(cast(E)_num, cast(E)_den, true);
    }


    auto opBinary(string op, U)(Rational!U r) if(!find(["+", "-", "*", "/", "%"], op).empty)
    {
       static if(op == "+"){
            auto gcd1 = gcd(_den, r._den);
            return rational(_num * (r._den / gcd1) + r._num * (_den / gcd1), _den / gcd1 * r._den);
        }
        else static if(op == "-"){
            auto gcd1 = gcd(_den, r._den);
            return rational(_num * (r._den / gcd1) - r._num * (_den / gcd1), _den / gcd1 * r._den);
        }
        else static if(op == "*"){
            auto gcd1 = gcd(_num, r._den);
            auto gcd2 = gcd(r._num, _den);
            return rational((_num/gcd1) * (r._num / gcd2), (_den/gcd2) * (r._den / gcd1), true);
        }
        else static if(op == "/"){
            auto gcd1 = gcd(_num, r._num);
            auto gcd2 = gcd(r._den, _den);
            if(r._num < 0)
                gcd1 = -gcd1;
            return rational((_num/gcd1) * (r._den / gcd2), (_den/gcd2) * (r._num / gcd1), true);
        }
        else static if(op == "%"){
            auto gcd1 = gcd(_den, r._den);
            return rational((_num * (r._den / gcd1)) % (r._num * (_den / gcd1)), _den / gcd1 * r._den);
        }
    }


    auto opBinary(string op, U)(U v) if(!isRationalType!U && !find(["+", "-", "*", "/", "%", "^^"], op).empty)
    {
        static if(op == "+")
            return rational(_num + _den * v, _den);
        else static if(op == "-")
            return rational(_num - _den * v, _den);
        else static if(op == "*")
            return rational(_num * v, _den);
        else static if(op == "/")
            return rational(_num, _den * v);
        else static if(op == "%")
            return rational(_num % (v * _den), _den);
        else static if(op == "^^"){
            if(v >= 0)
                return rational(_num ^^ v, _den ^^ v);
            else
                return rational(_den ^^ (-v), _num ^^ (-v));
        }
    }


    auto opBinaryRight(string op, U)(U v) if(!isRationalType!U && !find(["+", "-", "*", "/", "%"], op).empty)
    {
        static if(op == "+")
            return rational(_num + _den * v, _den);
        else static if(op == "-")
            return rational(_den * v - num, _den);
        else static if(op == "*")
            return rational(_num * v, _den);
        else static if(op == "/")
            return rational(v * _den, _num);
        else static if(op == "%")
            return rational((v * _den) % _num, _den);
    }


    void opOpAssign(string op, U)(Rational!U r) if(!find(["+", "-", "*", "/", "%"], op).empty)
    in{
        static if(op == "/")
            assert(r._num != 0);
    }
    body{
        static if(op == "+"){
            auto gcd1 = gcd(_den, r._den);
            _num = _num * (r._den / gcd1) + r._num * (_den / gcd1);
            _den = _den / gcd1 * r._den;
            reduce();
        }
        else static if(op == "-"){
            auto gcd1 = gcd(_den, r._den);
            _num = _num * (r._den / gcd1) - r._num * (_den / gcd1);
            _den = _den / gcd1 * r._den;
            reduce();
        }
        else static if(op == "*"){
            auto gcd1 = gcd(_num, r._den);
            auto gcd2 = gcd(r._num, _den);
            _num = (_num / gcd1) * (r._num / gcd2);
            _den = (_den / gcd2) * (r._den / gcd1);
        }
        else static if(op == "/"){
            auto gcd1 = gcd(_num, r._num);
            auto gcd2 = gcd(r._den, _den);

            if(r._num >= 0){
                _num = (_num / gcd1) * (r._den / gcd2);
                _den = (_den / gcd2) * (r._num / gcd1);
            }else{
                _num = -(_num / gcd1) * (r._den / gcd2);
                _den = -(_den / gcd2) * (r._num / gcd1);
            }
        }
        else static if(op == "%"){
            auto gcd1 = gcd(_den, r._den);
            _num = (_num * (r._den / gcd1)) % (r._num * (_den / gcd1));
            _den = _den / gcd1 * r._den;
            reduce();
        }
    }


    void opOpAssign(string op, U)(U v) if(!isRationalType!U && !find(["+", "-", "*", "/", "%", "^^"], op).empty)
        in{
        static if(op == "^^")
            assert(!(v < 0 && _num == 0));
    }
    body{
        static if(op == "+"){
            _num += _den * v;
        }else static if(op == "-"){
            _num -= _den * v;
        }else static if(op == "*"){
            _num *= v;
            reduce();
        }else static if(op == "/"){
            _den *= v;
            reduce();
        }else static if(op == "%"){
            _num %= _den * v;
            reduce();
        }else static if(op == "^^"){
            if(v >= 0){
                _num ^^= v;
                _den ^^= v;
            }else{
                if(_num >= 0){
                    _num = _den ^^ (-v);
                    _den = _num ^^ (-v);
                }else{
                    auto tmp = -_num;
                    _num = (-_den) ^^ (-v);
                    _den = (tmp) ^^ (-v);
                }
            }
        }
    }


    auto opCmp(U)(auto ref const U r) const if(!isRationalType!U){
        static if(is(typeof(_num - r * _den)))
            return _num - r * _den;
        else
            return (cast()_num) - (cast()r) * (cast()_den);
    }


    auto opCmp(U)(auto ref const Rational!U r) const {
        static if(is(typeof({auto _gcd = gcd(_den, r._den);}))){
            auto _gcd = gcd(_den, r._den);
            return (_num * (r._den / _gcd)) - (r._num * (_den / _gcd));
        }
        else{
            auto _gcd = gcd(cast()_den, cast()r._den);
            return ((cast()_num) * ((cast()r._den) / _gcd)) - ((cast()r._num) * ((cast()_den) / _gcd));
        }
    }


    bool opEquals(U)(auto ref const U v) const if(!isRationalType!U){
        return _den == 1 && _num == v;
    }


    bool opEquals(U)(auto ref const Rational!U r) const {
        return (_num == r._num) && (_den == r._den);
    }


    void toString(scope void delegate(const(char)[]) sink, FormatSpec!char fmt) const {
        if(fmt.nested.length != 0){
            formattedWrite(sink, fmt.nested, _num, _den);
        }else{
            formatValue(sink, _num, fmt);
            sink("/");
            formatValue(sink, _den, fmt);
        }
    }
}


Rational!(Unqual!(CommonType!(T, U))) rational(T, U)(T num, U den) pure nothrow @safe if(isLikeBuiltInInt!(Unqual!(CommonType!(T, U))))
{
    return Rational!(Unqual!(CommonType!(T, U)))(num, den, false);
}


///ditto
Rational!(Unqual!(CommonType!(T, U))) rational(T, U)(T num, U den) if(!isLikeBuiltInInt!(Unqual!(CommonType!(T, U))))
{
    return Rational!(Unqual!(CommonType!(T, U)))(num, den, false);
}


///ditto
Rational!(Unqual!T) rational(T)(T num) pure nothrow @safe if(isLikeBuiltInInt!(Unqual!T))
{
    return Rational!(Unqual!T)(num, 1);
}


///ditto
Rational!(Unqual!T) rational(T)(T num) if(!isLikeBuiltInInt!(Unqual!T))
{
    return Rational!(Unqual!T)(num, 1);
}


private
Rational!(Unqual!(CommonType!(T, U))) rational(T, U)(T num, U den, bool nonReduce) pure nothrow @safe if(isLikeBuiltInInt!(Unqual!(CommonType!(T, U))))
{
    return Rational!(Unqual!(CommonType!(T, U)))(num, den, nonReduce);
}


private
Rational!(Unqual!(CommonType!(T, U))) rational(T, U)(T num, U den, bool nonReduce) if(!isLikeBuiltInInt!(Unqual!(CommonType!(T, U))))
{
    return Rational!(Unqual!(CommonType!(T, U)))(num, den, nonReduce);
}


///ditto
alias per = rational;


unittest{   //int test
    import std.stdio;

    void foo() pure nothrow @safe
    {
        alias T = int;
        alias Rational!T R;
        alias R r;

        assert(R.init == r(0, 1));
        assert(R.init.den != 0);

        static assert(r(2, 15) == r(4, 5) % r(1, 6));   //CTFEable

        assert(3.per(2) == r(3, 2));    //num.per(den)

        //opUnary and cast test
        assert(-r(5) == r(-5, 1));
        assert(+r(5) == r(5));
        assert(++r(5, 13) == r(18, 13));
        assert(--r(5, 13) == r(-8, 13));
        assert(!r(0));
        assert(r(1));
        assert(cast(T)r(10, 3) == 3);

        //opBinary test
        assert(r(5, 6) + r(3, 8) == r(29, 24));
        assert(r(-1, 3) + r(3, 2) == r(7, 6));
        assert(r(1, 3) - r(4, 5) == r(-7, 15));
        assert(r(-1, 3) - r(-4, 5) == r(7, 15));
        assert(r(5, 6) * r(3, 8) == r(5, 16));
        assert(r(-1, 3) * r(3, 2) == r(-1, 2));
        assert(r(1, 3) / r(4, 5) == r(5, 12));
        assert(r(-1, 3) / r(-4, 5) == r(5, 12));
        assert(r(1, 3) % r(4, 5) == r(5, 15));
        assert(r(-1, 3) % r(-4, 5) == r(-5, 15));

        assert(r(5, 6) + 3 == r(23, 6));
        assert(r(-1, 3) + 3 == r(8, 3));
        assert(r(1, 3) - 3 == r(-8, 3));
        assert(r(-1, 3) - 3 == r(-10, 3));
        assert(r(5, 6) * 3 == r(5, 2));
        assert(r(-1, 3) * 3 == r(-1, 1));
        assert(r(1, 3) / 3 == r(1, 9));
        assert(r(-1, 3) / 3 == r(-1, 9));
        assert(r(1, 3) % 3 == r(1, 3));
        assert(r(-1, 3) % 3 == r(-1, 3));
        assert(r(2, 3) ^^ 3 == r(8, 27));
        assert(r(-1, 3) ^^ -3 == r(-27, 1));

        assert(3 + r(5, 6) == r(23, 6));
        assert(3 + r(-1, 3) == r(8, 3));
        assert(3 - r(1, 3) == r(8, 3));
        assert(3 - r(-1, 3) == r(10, 3));
        assert(3 * r(5, 6) == r(5, 2));
        assert(3 * r(-1, 3) == r(-1, 1));
        assert(3 / r(1, 3) == r(9, 1));
        assert(3 / r(-1, 3) == r(-9, 1));
        assert(3 % r(2, 3) == r(1, 3));
        assert(3 % r(-2, 3) == r(1, 3));

        {
            R r1 = 3;
            assert(r1 == r(3, 1));
        }

        auto r1 = r(5, 6);
        r1 += r(3, 8);
        assert(r1 == r(29, 24));
        r1 += r(3, 2);
        assert(r1 == r(65, 24));

        r1 = r(1, 3);
        r1 -= r(4, 5);
        assert(r1 == r(-7, 15));
        r1 -= r(-4, 5);
        assert(r1 == r(1, 3));

        r1 = r(5, 6);
        r1 *= r(3, 8);
        assert(r1 == r(5, 16));
        r1 *= r(3, 2);
        assert(r1 == r(15, 32));

        r1 = r(1, 3);
        r1 /= r(4, 5);
        assert(r1 == r(5, 12));
        r1 /= r(-4, 5);
        assert(r1 == r(-25, 48));

        r1 = r(4, 3);       //r(20, 15)
        r1 %= r(4, 5);      //r(12, 15)
        assert(r1 == r(8, 15));
        r1 %= r(-2, 5);     //r(-6, 15)
        assert(r1 == r(2, 15));

        
        r1 = r(-5, 6);
        r1 += 3;
        assert(r1 == r(13, 6));
        r1 += -3;
        assert(r1 == r(-5, 6));

        r1 = r(-1, 3);
        r1 -= 3;
        assert(r1 == r(-10, 3));
        r1 -= -3;
        assert(r1 == r(-1, 3));

        r1 = r(-5, 6);
        r1 *= 3;
        assert(r1 == r(-5, 2));
        r1 *= -3;
        assert(r1 == r(15, 2));

        r1 = r(-1, 3);
        r1 /= 4;
        assert(r1 == r(-1, 12));
        r1 /= -4;
        assert(r1 == r(1, 48));

        r1 = r(17, 2);      //r(51, 6)
        r1 %= 3;            //r(18, 6)
        assert(r1 == r(5, 2)); //r(25, 10)
        r1 = r(-25, 10);    //r(-25, 10)
        r1 %= r(2, 5);      //r(6, 10)
        assert(r1 == r(-1, 10));

        r1 = r(-1, 3);
        r1 ^^= 3;
        assert(r1 == r(-1, 27));
        r1 ^^= -2;
        assert(r1 == r(729, 1));

        assert(r1 == 729);
        assert(r1 < 799);
        assert(r1 < r(700*8, 3));
        assert(r1 > r(700*2, 3));
        assert(cast(Rational!long)r1 == r(729, 1));
    }

    foo();

    auto r1 = rational(729, 1);

    auto writer = appender!string;
    formattedWrite(writer, "%(%08d / %04d%)", r1);
    assert(writer.data == "00000729 / 0001");

    writer = appender!string;
    formattedWrite(writer, "%(%2$s/%1$s%)", r1);
    assert(writer.data == "1/729");

    writer = appender!string;
    formattedWrite(writer, "%08d", r1);
    assert(writer.data == "00000729/00000001");


    assert(-1.per(5) == rational(-1, 5));
}

unittest{   //BigInt test
    import std.stdio;

    alias T = BigInt;
    alias Rational!T R;
    alias R r;

    assert(R.init == r(0, 1));
    assert(-r(5) == r(-5, 1));
    assert(+r(5) == r(5));
    assert(++r(5, 13) == r(18, 13));
    assert(--r(5, 13) == r(-8, 13));
    assert(!r(0));
    assert(r(1));
    assert(cast(T)r(10, 3) == 3);

    //opBinary test
    assert(r(5, 6) + r(3, 8) == r(29, 24));
    assert(r(-1, 3) + r(3, 2) == r(7, 6));
    assert(r(1, 3) - r(4, 5) == r(-7, 15));
    assert(r(-1, 3) - r(-4, 5) == r(7, 15));
    assert(r(5, 6) * r(3, 8) == r(5, 16));
    assert(r(-1, 3) * r(3, 2) == r(-1, 2));
    assert(r(1, 3) / r(4, 5) == r(5, 12));
    assert(r(-1, 3) / r(-4, 5) == r(5, 12));
    assert(r(1, 3) % r(4, 5) == r(5, 15));
    assert(r(-1, 3) % r(-4, 5) == r(-5, 15));

    assert(r(5, 6) + 3 == r(23, 6));
    assert(r(-1, 3) + 3 == r(8, 3));
    assert(r(1, 3) - 3 == r(-8, 3));
    assert(r(-1, 3) - 3 == r(-10, 3));
    assert(r(5, 6) * 3 == r(5, 2));
    assert(r(-1, 3) * 3 == r(-1, 1));
    assert(r(1, 3) / 3 == r(1, 9));
    assert(r(-1, 3) / 3 == r(-1, 9));
    assert(r(1, 3) % 3 == r(1, 3));
    assert(r(-1, 3) % 3 == r(-1, 3));
    assert(r(2, 3) ^^ 3 == r(8, 27));
    assert(r(-1, 3) ^^ -3 == r(-27, 1));

    assert(3 + r(5, 6) == r(23, 6));
    assert(3 + r(-1, 3) == r(8, 3));
    assert(3 - r(1, 3) == r(8, 3));
    assert(3 - r(-1, 3) == r(10, 3));
    assert(3 * r(5, 6) == r(5, 2));
    assert(3 * r(-1, 3) == r(-1, 1));
    assert(3 / r(1, 3) == r(9, 1));
    assert(3 / r(-1, 3) == r(-9, 1));
    assert(3 % r(2, 3) == r(1, 3));
    assert(3 % r(-2, 3) == r(1, 3));

    {
        R r1 = 3;
        assert(r1 == r(3, 1));
    }

    auto r1 = r(5, 6);
    r1 += r(3, 8);
    assert(r1 == r(29, 24));
    r1 += r(3, 2);
    assert(r1 == r(65, 24));

    r1 = r(1, 3);
    r1 -= r(4, 5);
    assert(r1 == r(-7, 15));
    r1 -= r(-4, 5);
    assert(r1 == r(1, 3));

    r1 = r(5, 6);
    r1 *= r(3, 8);
    assert(r1 == r(5, 16));
    r1 *= r(3, 2);
    assert(r1 == r(15, 32));

    r1 = r(1, 3);
    r1 /= r(4, 5);
    assert(r1 == r(5, 12));
    r1 /= r(-4, 5);
    assert(r1 == r(-25, 48));

    r1 = r(4, 3);       //r(20, 15)
    r1 %= r(4, 5);      //r(12, 15)
    assert(r1 == r(8, 15));
    r1 %= r(-2, 5);     //r(-6, 15)
    assert(r1 == r(2, 15));

    
    r1 = r(-5, 6);
    r1 += 3;
    assert(r1 == r(13, 6));
    r1 += -3;
    assert(r1 == r(-5, 6));

    r1 = r(-1, 3);
    r1 -= 3;
    assert(r1 == r(-10, 3));
    r1 -= -3;
    assert(r1 == r(-1, 3));

    r1 = r(-5, 6);
    r1 *= 3;
    assert(r1 == r(-5, 2));
    r1 *= -3;
    assert(r1 == r(15, 2));

    r1 = r(-1, 3);
    r1 /= 4;
    assert(r1 == r(-1, 12));
    r1 /= -4;
    assert(r1 == r(1, 48));

    r1 = r(17, 2);      //r(51, 6)
    r1 %= 3;            //r(18, 6)
    assert(r1 == r(5, 2)); //r(25, 10)
    r1 = r(-25, 10);    //r(-25, 10)
    r1 %= r(2, 5);     //r(6, 10)
    assert(r1 == r(-1, 10));

    r1 = r(-1, 3);
    r1 ^^= 3;
    assert(r1 == r(-1, 27));
    r1 ^^= -2;
    assert(r1 == r(729, 1));

    assert(r1 == 729);
    assert(r1 == BigInt(729));
    assert(r1 <= BigInt(729));
    assert(!(r1 < r(729)));
    assert(r1 < r(700*8, 3));
    assert(r1 > r(700*2, 3));

    auto writer = appender!string;
    formattedWrite(writer, "%(%08d / %04d%)", r1);
    assert(writer.data == "00000729 / 0001");

    writer = appender!string;
    formattedWrite(writer, "%(%2$s/%1$s%)", r1);
    assert(writer.data == "1/729");

    writer = appender!string;
    formattedWrite(writer, "%08d", r1);
    assert(writer.data == "00000729/00000001");
}



template isRationalType(T){
    static if(is(T U == Rational!U))
        enum bool isRationalType = true;
    else
        enum bool isRationalType = false;
}

unittest{
    static assert(isRationalType!(Rational!int));
    static assert(isRationalType!(Rational!uint));
    static assert(isRationalType!(Rational!long));
    static assert(isRationalType!(Rational!ulong));
    static assert(isRationalType!(Rational!BigInt));
}

/*
Rational!int toRational()*/
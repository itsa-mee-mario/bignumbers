fun sum ([], [], c) = [c]
  | sum ([], y::ys, c) = 
    let
      val digit = y + c
      val carry = digit div 10
      val digit = digit mod 10
    in
      digit :: sum([], ys, carry)
    end
  | sum (x::xs, [], c) = 
    let
      val digit = x + c
      val carry = digit div 10
      val digit = digit mod 10
    in
      digit :: sum(xs, [], carry)
    end
  | sum (x::xs, y::ys, c) = 
    let
      val digit = x + y + c
      val carry = digit div 10
      val digit = digit mod 10
    in
      digit :: sum(xs, ys, carry)
    end;

sum([9, 9], [1], 0);

fun mult_list_digit([], [], c) = [c]
  | mult_list_digit([], [x], c) = [c]
  | mult_list_digit(y::ys, [x], c) =
  let
    val digit = y*x+c
    val carry = digit div 10
    val digit = digit mod 10
  in
    digit::mult_list_digit(ys, [x], carry)
  end;

mult_list_digit([1, 7, 3], [9], 0);

fun multiply([], [], last_op) = last_op
  | multiply([], y, last_op) = last_op
  | multiply(x, [], last_op) = last_op
  | multiply(x, y::ys, last_op) = 
  let
    val l = sum( mult_list_digit(x, [y], 0), last_op,  0)
  in
    multiply(0::x, ys, l)
  end;

multiply([9, 1], [2, 1], []);

sum([9,9], [~9,~9], 0);

fun eq ([], [], p) = p
  | eq ([x], [], p) = p
  | eq ([], [y], p) = p
  | eq (x::xs, y::ys, p) = 
  let
    val partial = if x=y then true else false
  in 
    eq(xs, ys, partial)
  end;

fun leq ([], [], p) = p
  | leq (x, [], p) = p
  | leq ([], y, p) = p
  | leq (x::xs, y::ys, p) = 
  let
    val partial = x<=y
  in 
    leq(xs, ys, partial)
  end;

fun lt ([], [], p) = p
  | lt(x, [], p) = p
  | lt ([], y, p) = p
  | lt (x::xs, y::ys, p) = 
  let
    val partial = x<y
  in 
    lt(xs, ys, partial)
  end;

fun gte ([], [], p) = p
  | gte(x, [], p) = p
  | gte ([], y, p) = p
  | gte (x::xs, y::ys, p) = 
  let
    val partial = x>=y
  in 
    gte(xs, ys, partial)
  end;

fun negate(x::xs) = ~x::negate(xs)
  | negate([]) = [];

negate([4, 5]);

fun sub(a, b) = if leq(a,b, true) then negate(sum(negate(a),b,0)) else sum(a, negate(b),0);

fun close_enough(A, B, error) =
let
  val lowerbound = sub(B, error)
  val upperbound = sum(B, error, 0)
in 
  if leq(lowerbound, A, false) andalso gte(upperbound, A, false) then true else false
end;

fun addDigits([], []) = []
  | addDigits([], ys) = ys
  | addDigits(xs, []) = xs
  | addDigits(x::xs, y::ys) = (x + y) :: addDigits(xs, ys);

fun splitAt(_, []) = ([], [])
  | splitAt(0, xs) = ([], xs)
  | splitAt(n, x::xs) =
    let
      val (ys, zs) = splitAt(n - 1, xs)
    in
      (x :: ys, zs)
    end;


fun multiply(x, y) =
  let
    fun shiftLeft([], _) = []
      | shiftLeft(xs, n) = 0 :: shiftLeft(xs, n - 1);

    fun multiplyHelper([], _) = []
      | multiplyHelper(_, []) = []
      | multiplyHelper(x::xs, [y]) =
        let
          val product = x * y;
          val carry = product div 10;
          val digit = product mod 10;
        in
          [digit, carry]
        end
      | multiplyHelper(x::xs, y) =
        let
          val half = length(y) div 2;
          val (y1, y0) = splitAt(half, y);
          val p0 = multiplyHelper(x::xs, y0);
          val p1 = multiplyHelper(shiftLeft(x::xs, half), y1);
          val p0' = if length(p0) = half then 0 :: p0 else p0;
          val p = addDigits(p0', p1);
        in
          addDigits(p, multiplyHelper(x::xs, y1))
        end;

    fun removeLeadingZeros([]) = []
      | removeLeadingZeros(0::xs) = removeLeadingZeros(xs)
      | removeLeadingZeros(xs) = xs;

    val result = removeLeadingZeros(multiplyHelper(x, y));
  in
    result
  end;

fun divModHelper(a, b, quotient, remainder) =
  let
    val a' = sub(a, b);
    val quotient' = sum(quotient, [1], 0);
  in
    if leq(a', b, true) then (quotient', a')
    else divModHelper(a', b, quotient', a')
  end;

fun divi(a, b) =
  let
    val (quotient, _) = divModHelper(a, b, [], []);
  in
    quotient
  end;

fun modi(a, b) =
  let
    val (_, remainder) = divModHelper(a, b, [], []);
  in
    remainder
  end;

fun mod2(a) =
  let
    val lastDigit = hd(a) modi 2;
  in
    [lastDigit]
  end;



fun divide(dividend, divisor) =
    let
        fun binarySearch(dividend, divisor, start, last) =
            if start > last then
                []
            else
                let
                    val mid = sum(start, last, 0)    (* Calculate the midpoint *)
                    val product = multiply(divisor, mid, [])    (* Calculate the product of divisor and mid *)
                    val comparison = leq(dividend, product, false)
                in
                    if comparison then
                        sum(mid, divide(sub(dividend, product), divisor), 0)    (* Recursively divide the remaining dividend *)
                    else
                        binarySearch(dividend, divisor, sum(mid, [1], 0), last)    (* Search in the higher range *)
                end
        
        val zero = [0]
        val one = [1]
        val dividendLength = length(dividend)
        val divisorLength = length(divisor)
        val start = replicate(dividendLength - divisorLength + 1, 0)    (* Initial start value for binary search *)
        val end = replicate(dividendLength, 9)    (* Initial end value for binary search *)
    in
        binarySearch(dividend, divisor, start, last)
    end;

шифр 419999 зс5^
ОЗУ 32^
АЦПУ 140^
ТРА 37^
ТЕЛЕ^
eeв1а3
*name Pascal
*call yesmemory
*full list
*system
*libra: 13
      subroutine doit(icrdin, serv)
      dimension icrdin(14),icrout(14)
      external serv
      call readfile(icrdin,icrout)
      call serv(icrout)
      return
      end
*pascal
program Main(input,output,result,pastel);(*=s7*) (*=Y+*)
%
%
%
Label 1,2,3,4,5;
%
%
(* main type: Gost context *)
  type
    TypeGostCtx = record
      roundkey: Array[1..32] of Integer;
      sbox: Array[1..8] of Array[0..15] of Integer;
    end;
    Arg = record  
      buflen, inplen: Integer;  
      dummy1, dummy2: Integer;  
      A: PACKED ARRAУ[1..140] ОF CHAR
    end;
    Card = PACKED ARRAУ[1..80] ОF CHAR;  
    Bitset = Set ОF 0..47;
    UInt32 = Integer;
    UInt16 = Integer;
    UInt8  = Integer;
    Intptr = @UInt32;
    Textptr = @Char;
    Ciphertext = File of Integer;
%
%
%
(* main variables : sboxes, key *)
  var 
    key: Array[1..8] of UInt32;
    (* GOST89 S-boxes *)
    s8: Array [1..16] of Integer; 
    s7: Array [1..16] of Integer; 
    s6: Array [1..16] of Integer;
    s5: Array [1..16] of Integer;
    s4: Array [1..16] of Integer;
    s3: Array [1..16] of Integer;
    s2: Array [1..16] of Integer;
    s1: Array [1..16] of Integer;
    (* GOST94 S-boxes *)
    sh8: Array [1..16] of Integer; 
    sh7: Array [1..16] of Integer; 
    sh6: Array [1..16] of Integer;
    sh5: Array [1..16] of Integer;
    sh4: Array [1..16] of Integer;
    sh3: Array [1..16] of Integer;
    sh2: Array [1..16] of Integer;
    sh1: Array [1..16] of Integer;
    (* constants *)
    magic : Real;
    mod31 : Integer;
    mod32 : Integer;
    (* password reading functionality *)
    pwd : Array[1..80] of Integer;
    pwdlen : Integer;
    buf : Arg;
    buf2 : Arg;
    R : Real;
    s : Char;    
    pastel: Array [0..25] ОF Bitset;  
    eqcheck : Integer;
    tryval : Integer;
    (* text related functionality *)
    f : Text;
    ctxt : Ciphertext;
    clen : Integer;
    fres : Text;
    arrctxt : Intptr;
    arrres : Intptr;
    arrstart : Intptr;
    result : Array[1..100] of Textptr;
    lens : Array[1..100] of Integer;
    curr, st : Textptr;
    str: Array[1..140] of Char; 
    (* other stuff *)
    sampletext: Intptr;
    samplecipher: Intptr;
    sampleres: Intptr;
    total : Integer;
    ctx: TypeGostCtx;
    msg: Array[1..2] of Integer;
    i,j,k,m,l: Integer;
    tmp: Integer;
    Procedure Pasred(var data : Arg); External; 
%
%
% 
(* GENERIC FUNCTIONS not related specifically to crypto *)
%
%
%
(* returns current time in integer format *)
  Function CurrTime : Integer;
  var x: real;
  begin 
    BESM(530010B); x := ;
    x := x * magic;
    x := x * 65536*65536;
    CurrTime := round(x * 1024);
  end;
%
%
%
(* addition modulo 2^32 *)
  Function Add32(x, y: UInt32): UInt32;
  var 
    mod32 : Integer;
  begin
    mod32 := 4294967296;
    Add32 := (x + y) mod (mod32);
  end;
%
%
%
(* 
  addition modulo 2^256 of input blocks,
  long arithmetic on UInt32 arrays,
  the result is stored in ss  
*)
  Procedure Add256(
    var ss : Array[1..8] of UInt32;
    xs : Array[1..8] of UInt32
  );
  var 
    i : Integer;
    j : Integer;
    carry : Integer;
    mod32 : Integer;
    curr : Integer;
  begin 
    mod32 := 4294967296;
    curr := 0;
    carry := 0;
    for i := 1 to 8 do 
    begin
      j := 8 - i + 1; 
      curr := (ss[j] + xs[j] + carry);
      ss[j] := curr mod mod32;
      carry := curr div mod32;
    end;
  end;
%
%
%
(* SWAP halves *)
  Procedure Swap(var xs : Array[1..2] of UInt32);
  var 
    tmp : UInt32;
  begin
    tmp := xs[1];
    xs[1] := xs[2];
    xs[2] := tmp;
  end;
%
%
%
  Function Reverse(x : UInt32) : UInt32;
  var 
    i : Integer;
    curr : UInt32;
  begin 
    curr := 0;
    for i := 1 to 32 do
    begin 
      curr := curr * 2;
      curr := curr + (x mod 2);
      x := x div 2;
    end; 
    Reverse := curr;
  end;
%
%
%
  Procedure PrintArray(xs : Intptr; len : Integer);
  var 
    i : Integer;
  begin 
    for i := 1 to len do 
    begin 
      WriteLn(' ', xs@);
      xs := succ(xs);
    end;
  end;
%
%
%
(* XORing two integer numbers *)
  Function Xor(x, y : Integer) : Integer;
  var 
    val: Integer;
    cur: Integer;
    res: Integer;
  begin
    res := 0;
    val := 1;
    while ((x <> 0) or (y <> 0)) do
    begin
      cur := ((x mod 2) + (y mod 2)) mod 2;
      res := cur * val + res;
      x := x div 2;
      y := y div 2;
      val := val * 2;
    end;
    Xor := res;
  end;
%
%
%
(* cyclic rotation by 11 positions modulo 2^32 *)
  Function Rot11(x : UInt32) : UInt32;
  var 
    i : Integer;
    res : UInt32;
    firstbit : Integer;
  begin 
    (* 2^31 and 2^32 *)
    res := x;
    for i := 1 to 11 do 
    begin
        firstbit := res div mod31;
        res := (res * 2) mod (mod32);
        res := Xor(res, firstbit);
    end;
    Rot11 := res;
  end;
%
%
%
(* initialize GOST context *)
  Procedure InitGostCtx(
    var ctx: TypeGostCtx;
    key: Array[1..8] of Integer;
    s8: Array[1..16] of Integer;  
    s7: Array[1..16] of Integer;  
    s6: Array[1..16] of Integer; 
    s5: Array[1..16] of Integer;  
    s4: Array[1..16] of Integer;  
    s3: Array[1..16] of Integer;  
    s2: Array[1..16] of Integer;  
    s1: Array[1..16] of Integer);
  var
    i: Integer;
  begin
    ctx.sbox[1] := s1;
    ctx.sbox[2] := s2;
    ctx.sbox[3] := s3;
    ctx.sbox[4] := s4;
    ctx.sbox[5] := s5;
    ctx.sbox[6] := s6;
    ctx.sbox[7] := s7;
    ctx.sbox[8] := s8;
    for i := 1 to 8 do
    begin
      ctx.roundkey[i] := key[i];
      ctx.roundkey[i + 8] := key[i];
      ctx.roundkey[i + 16] := key[i];
      ctx.roundkey[33 - i] := key[i];
    end
  end;
%
%
%
(* nonlinear layer of GOST89 algorithm *)
  Function nonlinear(ctx: TypeGostCtx; x: UInt32): UInt32;
  var 
    i: Integer;
    res: UInt32;
    curr: UInt32;
    val: UInt32;
  begin
    res := 0;
    val := 1;
    for i := 1 to 8 do 
    begin 
      (* take 4 least significant bits *)
      curr := x mod 16;
      (* apply nonlinear Sbox *)
      curr := ctx.sbox[9-i][curr];
      res := res + curr * val;
      val := val * 16;
      x := x div 16;
    end;
    nonlinear := res
  end;
%
%
%
(* xor + nonlinear + linear composition *)
  Function LSX(ctx: TypeGostCtx; x, round: UInt32): UInt32;
  var 
    res: UInt32;
  begin 
    res := Add32(ctx.roundkey[round], x);
    res := nonlinear(ctx, res);
    res := Rot11(res);
    LSX := res
  end;
%
%
%
(* one round of Feistel Network *)
  Procedure Feistel(
    ctx: TypeGostCtx; 
    var txt: Array[1..2] of UInt32; 
    i: Integer);
  var 
    left: UInt32;
    right: UInt32;
    tmp: UInt32;
  begin
    left := txt[1];
    right := txt[2];
    tmp := LSX(ctx, txt[2], i);
    txt[1] := right;
    txt[2] := Xor(left, tmp);
  (*
    txt[2] := LSX(ctx, txt[2], i);
    Swap(txt);
  *)
  end;
%
%
%
(* 
  Full encryption procedure, works in-place: 
  the result of the encryption is stored in txt
*)
  Procedure EncryptBlock(
    ctx: TypeGostCtx;
    var txt: Array[1..2] of UInt32
  );
  var
    i: Integer;
    tmp : UInt32;
  begin
    for i := 1 to 32 do
    begin
      Feistel(ctx, txt, i);
    end;
    tmp := txt[1];
    txt[1] := txt[2];
    txt[2] := tmp;
  end;
%
%
%
  Procedure DecryptBlock(
    ctx: TypeGostCtx;
    var txt: Array[1..2] of Integer
  );
  var
    i: Integer;
    tmp : Integer;
  begin
    for i := 1 to 32 do
    begin
      Feistel(ctx, txt, 32-i+1);
    end;
    tmp := txt[1];
    txt[1] := txt[2];
    txt[2] := tmp;
  end;
%
%
%
  Procedure EncryptIV(
    ctx : TypeGostCtx;
    txt : Intptr;
    res : Intptr;
    len : Integer;
    startvalue : UInt32
  );
  var 
    i : Integer;
    tmp : UInt32;
    blocknum : Integer;
    counter : Array[1..2] of UInt32;
  begin 
    blocknum := len div 2;
    counter[1] := startvalue;
    counter[2] := 0;
    (* main encryption part *)
    for i := 1 to blocknum do 
    begin 
      counter[2] := counter[2] + 1;
      EncryptBlock(ctx, counter);
      tmp := Xor(txt@, counter[1]);
      res@ := tmp;
      txt := succ(txt);
      res := succ(res);
      tmp := Xor(txt@, counter[2]);
      res@ := tmp;
      if (i <> blocknum) then
      begin
        txt := succ(txt);
        res := succ(res);
      end;
    end;
    (* only if last block is incomplete *)
    if (len mod 2 = 1) then 
    begin 
      txt := succ(txt);
      res := succ(res);
      counter[2] := counter[2] + 1;
      EncryptBlock(ctx, counter);
      tmp := Xor(txt@, counter[1]);
      res@ := tmp;
    end;
  end;
%
%
%
  Procedure EncryptCTR(
    ctx : TypeGostCtx;
    txt : Intptr;
    res : Intptr;
    len : Integer
  );
  var 
    iv : Integer;
  begin 
    iv := CurrTime;
    res@ := iv;
    res := succ(res);
    EncryptIV(ctx,txt,res,len,iv);
  end;
%
%
%
    Procedure FileEncryptIV(
        ctx : TypeGostCtx;
        iv : UInt32;
        var f : Text;
        var ctxt : Ciphertext;
        var clen : Integer
    );
    var 
        i : Integer;
        x : Char;
        tmp : UInt32;
        counter : Array[1..2] of UInt32;
        gamma : Array[1..2] of UInt32;
    begin 
        counter[1] := iv;
        counter[2] := 0;
        (* main encryption part *)
        While (Eof(f) <> true) do
        begin
            counter[2] := counter[2] + 1;
            gamma[1] := counter[1];
            gamma[2] := counter[2];
            EncryptBlock(ctx, gamma);
            Read(f,x);
            tmp := Xor(Ord(x), gamma[1]);
            Write(ctxt, tmp);
            clen := clen + 1;
            if (Eof(f) <> true) then 
            begin 
                Read(f,x);
                tmp := Xor(Ord(x), gamma[2]);
                Write(ctxt, tmp);
                clen := clen + 1;
            end;
        end;
    end;
%
%
%
    Procedure MessageEncryptIV(
        ctx : TypeGostCtx;
        iv : UInt32;
        var f : Text;
        var ctxt : Ciphertext
    );
    var 
        i : Integer;
        x : Char;
        tmp : UInt32;
        counter : Array[1..2] of UInt32;
        gamma : Array[1..2] of UInt32;
    begin 
        counter[1] := iv;
        counter[2] := 0;
        (* main encryption part *)
        While (Eof(f) <> true) do
        begin
            counter[2] := counter[2] + 1;
            gamma[1] := counter[1];
            gamma[2] := counter[2];
            EncryptBlock(ctx, gamma);
            Read(f,x);
            tmp := Xor(Ord(x), gamma[1]);
            Write(ctxt, tmp);
            if (Eof(f) <> true) then 
            begin 
                Read(f,x);
                tmp := Xor(Ord(x), gamma[2]);
                Write(ctxt, tmp);
            end;
        end;
    end;
%
%
%
    Procedure FileDecryptIV(
        ctx : TypeGostCtx;
        iv : UInt32;
        var ctxt : Ciphertext;
        var fres : Text;
        var clen : Integer
    );
    var 
        i : Integer;
        x : UInt32;
        tmp : UInt32;
        counter : Array[1..2] of UInt32;
        gamma : Array[1..2] of UInt32;
    begin 
        i := 0;
        counter[1] := iv;
        counter[2] := 0;
        (* main decryption part *)
        While (i < clen) do
        begin
            i := i + 1;
            counter[2] := counter[2] + 1;
            gamma[1] := counter[1];
            gamma[2] := counter[2];
            EncryptBlock(ctx, gamma);
            Read(ctxt, x);
            tmp := Xor(x, gamma[1]);
            Write(fres, Chr(tmp));
            if (i < clen) then 
            begin 
                Read(ctxt, x);
                tmp := Xor(x, gamma[2]);
                Write(fres, Chr(tmp));
                i := i + 1;
            end;
        end;
        WriteLn(fres);
    end;
%
%
%
    Procedure MessageDecryptIV(
        ctx : TypeGostCtx;
        iv : UInt32;
        var ctxt : Ciphertext;
        var fres : Text
    );
    var 
        x : UInt32;
        tmp : UInt32;
        counter : Array[1..2] of UInt32;
        gamma : Array[1..2] of UInt32;
    begin 
        counter[1] := iv;
        counter[2] := 0;
        (* main decryption part *)
        While not (Eof(ctxt)) do
        begin
            counter[2] := counter[2] + 1;
            gamma[1] := counter[1];
            gamma[2] := counter[2];
            EncryptBlock(ctx, gamma);
            Read(ctxt, x);
            tmp := Xor(x, gamma[1]);
            Write(fres, Chr(tmp));
            if not (Eof(ctxt)) then 
            begin 
                Read(ctxt, x);
                tmp := Xor(x, gamma[2]);
                Write(fres, Chr(tmp));
            end;
        end;
        WriteLn(fres);
    end;
%
%
%
    Procedure EncryptFile(
        ctx : TypeGostCtx;
        var f : Text;
        var ctxt : Ciphertext;
        var clen : Integer
    );
    var 
        iv : UInt32;
    begin 
        iv := CurrTime;
        Write(ctxt, iv);
        FileEncryptIV(ctx, iv, f, ctxt, clen);
    end;
%
%
%
  Procedure EncryptMessage(
        ctx : TypeGostCtx;
        var f : Text;
        var ctxt : Ciphertext
    );
    var 
        iv : UInt32;
    begin 
        iv := CurrTime;
        Write(ctxt, iv);
        MessageEncryptIV(ctx, iv, f, ctxt);
    end;
%
%
%
    Procedure DecryptFile(
        ctx : TypeGostCtx;
        var ctxt : Ciphertext;
        var fres : Text;
        var clen : Integer
    );
    var 
        iv : UInt32;
    begin
        Read(ctxt, iv);
        FileDecryptIV(ctx, iv, ctxt, fres, clen);
    end;
%
%
%
    Procedure DecryptMessage(
        ctx : TypeGostCtx;
        var ctxt : Ciphertext;
        var fres : Text
    );
    var 
        iv : UInt32;
    begin
        Read(ctxt, iv);
        MessageDecryptIV(ctx, iv, ctxt, fres);
    end;
%
%
%
    Procedure EncryptToArray(
        ctx : TypeGostCtx;
        var f : Text;
        var arrres : Intptr
    );
    var 
        iv : UInt32;
        i : Integer;
        x : Char;
        tmp : UInt32;
        counter : Array[1..2] of UInt32;
        gamma : Array[1..2] of UInt32;
    begin 
        iv := CurrTime;
        arrres@ := iv;
        arrres := succ(arrres);
        counter[1] := iv;
        counter[2] := 0;
        (* main encryption part *)
        While (Eof(f) <> true) do
        begin
            counter[2] := counter[2] + 1;
            gamma[1] := counter[1];
            gamma[2] := counter[2];
            EncryptBlock(ctx, gamma);
            Read(f,x);
            tmp := Xor(Ord(x), gamma[1]);
            arrres@ := tmp;
            arrres := succ(arrres);
            if (Eof(f) <> true) then 
            begin 
                Read(f,x);
                tmp := Xor(Ord(x), gamma[2]);
                arrres@ := tmp;
                arrres := succ(arrres);
            end;
        end;
    end;
%
%
%
    Procedure DecryptArray(
        ctx : TypeGostCtx;
        var arr : Intptr;
        var f : Text;
        len : Integer
    );
    var 
        iv : UInt32;
        s : Char;
        i : Integer;
        blocknum : Integer;
        x : Char;
        tmp : UInt32;
        counter : Array[1..2] of UInt32;
        gamma : Array[1..2] of UInt32;
    begin 
        iv := arr@;
        arr := succ(arr);
        counter[1] := iv;
        counter[2] := 0;
        blocknum := len div 2;
        (* main decryption part *)
        for i := 1 to blocknum do 
        begin 
            counter[2] := counter[2] + 1;
            gamma[1] := counter[1];
            gamma[2] := counter[2];
            EncryptBlock(ctx, gamma);
            tmp := Xor(arr@, gamma[1]);
            arr := succ(arr);
            s := Chr(tmp);
            Write(f, s);
            tmp := Xor(arr@, gamma[2]);
            s := Chr(tmp);
            Write(f, s);
            if (i <> blocknum) then
            begin
                arr := succ(arr);
            end;
        end;
        (* only if last block is incomplete *)
        if (len mod 2 = 1) then 
        begin 
            arr := succ(arr);
            counter[2] := counter[2] + 1;
            gamma[1] := counter[1];
            gamma[2] := counter[2];
            EncryptBlock(ctx, gamma);
            tmp := Xor(arr@, gamma[1]);
            s := Chr(tmp);
            Write(f, s);
        end;
    end;
%
%
%
  Procedure DecryptCTR(
    ctx : TypeGostCtx;
    ctxt : Intptr;
    res : Intptr;
    len : Integer
  );
  var 
    iv : Integer;
  begin 
    iv := ctxt@;
    ctxt := succ(ctxt);
    EncryptIV(ctx,ctxt,res,len,iv);
  end;
%
%
%
  Function TestEquality(x, y : Integer) : Integer;
  begin 
    Write(' ');
    Write(x);
    Write(', Expected: ');
    Write(y);
    if (x = y) then 
    begin
      WriteLn('; SUCCESS');
      TestEquality := 1;
    end
    else 
    begin
      WriteLn('; FAIL');
      TestEquality := 0;
    end;
  end;
%
%
%
  Procedure TestBattery(x, y : Integer);
  begin 
    if (x = y) then 
    begin
      WriteLn('TEST BATTERY RESULT: SUCCESS');
    end
    else 
    begin
      WriteLn('TEST BATTERY RESULT: FAIL');
    end;
  end;
%
%
%
  Procedure TestGost89(
    s8: Array[1..16] of Integer;  
    s7: Array[1..16] of Integer;  
    s6: Array[1..16] of Integer; 
    s5: Array[1..16] of Integer;  
    s4: Array[1..16] of Integer;  
    s3: Array[1..16] of Integer;  
    s2: Array[1..16] of Integer;  
    s1: Array[1..16] of Integer);
  var
    key : Array[1..8] of UInt32;
    ctx : TypeGostCtx;
    k : Integer;
    m : Integer;
    res : Integer;
    curr : Integer;
    i : Integer;
    total : Integer;
  begin 
    for i := 1 to 8 do 
    begin 
      key[i] := 0;
    end;
    WriteLn('Initializing GOST context');
    InitGostCtx(ctx,key,s8,s7,s6,s5,s4,s3,s2,s1);
    WriteLn(' Successful initialization');
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    (* 4256789809 = 0xfdb97531*)
    (* 706309940 = 0x2a196f34*)
    WriteLn('Testing nonlinear transformation:');
    WriteLn('-----------------');
    total := 0;
    m := 4256789809;
    m := nonlinear(ctx, m);
    total := total + TestEquality(m, 706309940);
    m := nonlinear(ctx, m);
    total := total + TestEquality(m, 3956928570);
    m := nonlinear(ctx, m);
    total := total + TestEquality(m, 2956573501);
    TestBattery(total, 3);
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    WriteLn('Testing Rot11:');
    WriteLn('-----------------');
    m := 2882400001;
    m := Rot11(m);
    total := total + TestEquality(m, 1870138718);
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    WriteLn('Testing Add32:');
    WriteLn('-----------------');
    k := 2271560481;
    m := 4275878552;
    res := Add32(k, m);
    total := total + TestEquality(res, 2252471737);
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    (* 0xfedcba98 = 4275878552 *)
    (* 0x87654321 = 2271560481 *)
    (* 0xfdcbc20c = 4257989132 *)
    WriteLn('Testing Feistel Round:');
    WriteLn('-----------------');
    msg[1] := 0;
    msg[2] := 4275878552;
    ctx.roundkey[1] := 2271560481;
    Feistel(ctx,msg,1);
    total := total + TestEquality(msg[2], 4257989132);
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    WriteLn('FULL GOST TEST');
    WriteLn('-----------------');
    (* msg = 0xfedcba98 0x76543210 *)
    msg[1] := 4275878552;
    msg[2] := 1985229328;
    key[1] := 4293844428;
    key[2] := 3148519816;
    key[3] := 2003195204;
    key[4] := 857870592;
    key[5] := 4042388211;
    key[6] := 4109760247;
    key[7] := 4177132283;
    key[8] := 4244504319;
    InitGostCtx(ctx,key,s8,s7,s6,s5,s4,s3,s2,s1);
    EncryptBlock(ctx, msg);
    total := 0;
    total := total + TestEquality(msg[1], 1323893221);
    total := total + TestEquality(msg[2], 3268987453);
    TestBattery(total, 2);
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    WriteLn('Test complete');
  end;
%
%
%
(*
  Procedure Gost94Ctx(
    var ctx : TypeGostCtx;
    key : Array[1..8] of UInt32;
    s8: Array[1..16] of Integer;  
    s7: Array[1..16] of Integer;  
    s6: Array[1..16] of Integer; 
    s5: Array[1..16] of Integer;  
    s4: Array[1..16] of Integer;  
    s3: Array[1..16] of Integer;  
    s2: Array[1..16] of Integer;  
    s1: Array[1..16] of Integer
  );
  begin 
    InitGostCtx(ctx,key,s8,s7,s6,s5,s4,s3,s2,s1);
  end;
*)

  Procedure Gost94Ctx(
    var ctx : TypeGostCtx
  );
  var 
    key : Array[1..8] of UInt32;
    i : Integer;
  begin 
    for i:= 1 to 8 do
    begin 
      key[i] := 0;
    end;
    InitGostCtx(ctx,key,sh8,sh7,sh6,sh5,sh4,sh3,sh2,sh1);
  end;
%
%
%
  Procedure SetKey(
    var ctx : TypeGostCtx;
    key : Array[1..8] of UInt32
  );
  var
    i : Integer;
  begin 
    for i := 1 to 8 do
    begin
      ctx.roundkey[i] := key[i];
      ctx.roundkey[i + 8] := key[i];
      ctx.roundkey[i + 16] := key[i];
      ctx.roundkey[33 - i] := key[i];
    end
  end;
%
%
%
(* GOST94 subfunctions *)
(*   
  transformation of the form 
  (x8 x7 x6 x5 x4 x3 x2 x1) 
  -> (x5 xor x7, x6 xor x8, x8 x7 x6 x5 x4 x3) 
  in-place: xs is mutated
*)
  Procedure Alin(var xs : Array[1..8] of UInt32);
  var 
    x1 : Integer;
    x2 : Integer;
  begin 
    x1 := Xor(xs[5], xs[7]);
    x2 := Xor(xs[6], xs[8]);
    xs[8] := xs[6];
    xs[7] := xs[5];
    xs[6] := xs[4];
    xs[5] := xs[3];
    xs[4] := xs[2];
    xs[3] := xs[1];
    xs[2] := x2;
    xs[1] := x1;
  end;
%
%
%
(*
  function for the permutation 
  {1, ..., 32} -> {1, ..., 32}
*)
  Function Phi(x : Integer) : Integer;
  var 
    i : Integer;
    k : Integer;
    res : Integer;
  begin
    i := (x - 1) mod 4;
    k := ((x - i - 1) div 4) + 1;
    res := 8 * i + k;
    Phi := res;
  end;
%
%
%
(* 
  unpacking 32-bit integer array xs in 8-bit array ys
  in-place: ys is mutated
*)
  Procedure Unpack8(
    xs : Array[1..8] of UInt32;
    var ys : Array[1..32] of UInt8);
  var 
    i : Integer;
    j : Integer;
    curr : UInt32;
  begin 
    for i := 0 to 7 do
    begin 
      curr := xs[i+1];
      for j := 1 to 4 do 
      begin
        ys[4*i + (5-j)] := curr mod 256;
        curr := curr div 256;
      end;
    end;
  end;
%
%
%
(* 
  packing 8-bit integer array xs in 32-bit array ys
  in-place: ys is mutated
*)
  Procedure Pack8(
    xs : Array[1..32] of UInt8;
    var ys : Array[1..8] of UInt32);
  var 
    i : Integer;
    j : Integer;
    curr : UInt32;
  begin 
    for i := 0 to 7 do
    begin 
      curr := 0;
      for j := 1 to 4 do 
      begin
        curr := curr * 256;
        curr := curr + xs[4*i + j];
      end;
      ys[i + 1] := curr;
    end;
  end;
%
%
%
(* 
  unpacking 32-bit integer array xs in 16-bit array ys
  in-place: ys is mutated
*)
  Procedure Unpack16(
    xs : Array[1..8] of UInt32;
    var ys : Array[1..16] of UInt16);
  var 
    i : Integer;
    j : Integer;
    curr : UInt32;
    mod16 : Integer;
  begin 
    mod16 := 65536;
    for i := 0 to 7 do
    begin 
      curr := xs[i+1];
      for j := 1 to 2 do 
      begin
        ys[2*i + (3 - j)] := curr mod mod16;
        curr := curr div mod16;
      end
    end;
  end;
%
%
%
(* 
  packing 16-bit integer array xs in 32-bit array ys
  in-place: ys is mutated
*)
  Procedure Pack16(
    xs : Array[1..16] of UInt16;
    var ys : Array[1..8] of UInt32);
  var 
    i : Integer;
    j : Integer;
    curr : UInt32;
    mod16 : Integer;
  begin 
    mod16 := 65536;
    for i := 0 to 7 do
    begin 
      curr := 0;
      for j := 1 to 2 do 
      begin
        curr := curr * mod16;
        curr := curr + xs[2*i + j];
      end;
      ys[i + 1] := curr;
    end;
  end;
%
%
%
(* 
  linear transformation 
  Array[UInt32] -> Array[UInt8] -> 
  -> permutation -> Array[UInt32]
  in-place: xs is modified
*)
  Procedure Plin(var xs : Array[1..8] of UInt32);
  var 
    res : Array[1..32] of UInt8;
    tmp : Array[1..32] of UInt8;
    i : Integer;
    idx : Integer;
  begin 
    (* UInt8 inner representation *)
    Unpack8(xs, res);
    for i := 1 to 32 do 
    begin 
      (* in the 1st cell we must put xi_{Phi(32)} etc *)
      (* i.e. tmp[i] <- tmp[32 - Phi(32-i+1) + 1] *) 
      idx := 32 - Phi(32 - i + 1) + 1;
      tmp[i] := res[idx];
    end;
    Pack8(tmp, xs);
  end;
%
%
%
(* 
  linear transformation 
  Array[UInt32] -> Array[UInt16] -> 
  -> generic feistel round -> Array[UInt32]
  in-place: xs is modified
*)
  Procedure Psi(var xs : Array[1..8] of UInt32);
  var 
    res : Array[1..16] of UInt16;
    i : Integer;
    j : Integer;
    fst : Integer;
    mod16 : Integer;
    curr : UInt32;
  begin
    Unpack16(xs, res);
    fst := Xor(Xor(Xor(res[16], res[15]), res[14]), res[13]);
    fst := Xor(Xor(fst, res[4]), res[1]);
    (* res[16] <- res[15], res[15] <- res[14], etc *)
    for i := 1 to 15 do 
    begin 
      res[16 - i + 1] := res[16 - i];
    end;
    res[1] := fst;
    Pack16(res, xs);
  end;
%
%
%
(* XORing arrays xs, ys of length 8 *)
(* in-place: store result in zs *)
  Procedure XorArray(
    xs : Array[1..8] of UInt32;
    ys : Array[1..8] of UInt32;
    var zs : Array[1..8] of UInt32
  );
  var 
    i : Integer;
  begin 
    for i := 1 to 8 do 
    begin 
      zs[i] := Xor(xs[i], ys[i]);
    end; 
  end;
%
%
%
(*
  in-place: xs is modified
*)
  Procedure AddConstC3(var xs : Array[1..8] of UInt32);
  var 
    cs : Array[1..8] of UInt32;
    i : Integer;
  begin 
    (* 0xff00ffff *)
    cs[1] := 4278255615;
    (* 0x000000ff *)
    cs[2] := 255;
    (* 0xff0000ff *)
    cs[3] := 4278190335;
    (* 0x00ffff00 *)
    cs[4] := 16776960;
    (* 0x00ff00ff *)
    cs[5] := 16711935;
    (* 0x00ff00ff *)
    cs[6] := 16711935;
    (* 0xff00ff00 *)
    cs[7] := 4278255360;
    (* 0xff00ff00 *)
    cs[8] := 4278255360;
    for i := 1 to 8 do 
    begin 
      xs[i] := Xor(xs[i], cs[i]);
    end; 
  end;
%
%
%
(*
  internal keygen procedure
  in-place: K1, .., K4 are modified
*)
  Procedure Keygen(
    hs : Array[1..8] of UInt32;
    ms : Array[1..8] of UInt32;
    var K1 : Array[1..8] of UInt32;
    var K2 : Array[1..8] of UInt32;
    var K3 : Array[1..8] of UInt32;
    var K4 : Array[1..8] of UInt32
  );
  var
    us : Array[1..8] of UInt32;
    vs : Array[1..8] of UInt32;
    i : Integer;
  begin 
    for i := 1 to 8 do 
    begin 
      us[i] := hs[i];
      vs[i] := ms[i];
    end;
    (* i = 1 *)
    XorArray(us, vs, K1);
    Plin(K1);
    (* i = 2 *)
    Alin(us);
    Alin(vs);
    Alin(vs);
    XorArray(us, vs, K2);
    Plin(K2);
    (* i = 3 *)
    Alin(us);
    (* here we must add Const *)
    AddConstC3(us);
    Alin(vs);
    Alin(vs);
    XorArray(us, vs, K3);
    Plin(K3);
    (* i = 4 *)
    Alin(us);
    Alin(vs);
    Alin(vs);
    XorArray(us, vs, K4);
    Plin(K4);
  end;
%
%
%
(* 
  hs : current internal value 
  ms : message block to be processed
  in-place: hs is modified
*)
  Procedure EncryptStep(
    var hs : Array[1..8] of UInt32;
    ms : Array[1..8] of UInt32;
    var ctx : TypeGostCtx
  );
  var 
    K1 : Array[1..8] of UInt32;
    K2 : Array[1..8] of UInt32;
    K3 : Array[1..8] of UInt32;
    K4 : Array[1..8] of UInt32;
    curr : Array[1..2] of UInt32;
    i : Integer;
  begin 
    Keygen(hs, ms, K1, K2, K3, K4);
    (* 
      first block 
    *)
    SetKey(ctx, K4);
    curr[1] := hs[1];
    curr[2] := hs[2];
    EncryptBlock(ctx, curr);
    hs[1] := curr[1];
    hs[2] := curr[2];
    (* 
      second block 
    *)
    SetKey(ctx, K3);
    curr[1] := hs[3];
    curr[2] := hs[4];
    EncryptBlock(ctx, curr);
    hs[3] := curr[1];
    hs[4] := curr[2];
    (* 
      third block 
    *)
    SetKey(ctx, K2);
    curr[1] := hs[5];
    curr[2] := hs[6];
    EncryptBlock(ctx, curr);
    hs[5] := curr[1];
    hs[6] := curr[2];
    (* 
      fourth block 
    *)
    SetKey(ctx, K1);
    curr[1] := hs[7];
    curr[2] := hs[8];
    EncryptBlock(ctx, curr);
    hs[7] := curr[1];
    hs[8] := curr[2];
  end;
%
%
%
(* 
  final linear step transformation,
  hs : current internal state,
  ss : encrypted value,
  ms : message block to be processed,
  in-place: hs is modified
*)
  Procedure LinearStep(
    var hs : Array[1..8] of UInt32;
    ss : Array[1..8] of UInt32;
    ms : Array[1..8] of UInt32
  );
  var 
    xs : Array[1..8] of UInt32;
    tmp : Array[1..8] of UInt32;
    i : Integer;
  begin 
    for i := 1 to 8 do 
    begin 
      xs[i] := ms[i];
    end;
    for i := 1 to 12 do 
    begin 
      Psi(ss);
    end;
    XorArray(xs, ss, tmp);
    for i := 1 to 8 do 
    begin 
      xs[i] := tmp[i];
    end;
    Psi(xs);
    XorArray(xs, hs, tmp);
    for i := 1 to 8 do 
    begin 
      xs[i] := tmp[i];
    end;
    for i := 1 to 61 do 
    begin 
      Psi(xs);
    end;
    for i := 1 to 8 do 
    begin
      hs[i] := xs[i];
    end;
  end;
%
%
%
(* 
  hash step calculation
  in-place: hs is modified
*)
  Procedure HashStep(
    var hs : Array[1..8] of UInt32;
    ms : Array[1..8] of UInt32;
    ctx : TypeGostCtx
  );
  var 
    ss : Array[1..8] of UInt32;
    i : Integer;
  begin 
    for i := 1 to 8 do 
    begin 
      ss[i] := ms[i];
    end;
    EncryptStep(hs, ss, ctx);
    LinearStep(hs, ss, ms);
  end;
%
%
%
  Procedure HashMessage(
    msg : Intptr;
    len : Integer;
    var res : Array[1..8] of UInt32
  );
  var 
    hs : Array[1..8] of UInt32;
    xs : Array[1..8] of UInt32;
    sigma : Array[1..8] of UInt32;
    lenblk : Array[1..8] of UInt32;
    blocknum : Integer;
    needpad : Integer;
    i : Integer;
    imax : Integer;
    j : Integer;
    ctx : TypeGostCtx;
  begin 
    Gost94Ctx(ctx);
    needpad := len mod 8;
    blocknum := len div 8;
    for i := 1 to 8 do 
    begin 
      hs[i] := 0;
      sigma[i] := 0;
      lenblk[i] := 0;
    end;
    (* 
      here we assume that the message to be hashed is 
      no longer than 2^32 bits 
    *)
    lenblk[8] := 32 * len;
    (* main cycle: process message by blocks *)
    for i := 1 to blocknum do 
    begin 
      (* read current message chunk *)
      for j := 1 to 8 do 
      begin
        xs[j] := msg@;
        msg := succ(msg);
      end;
      (*
        only for debugging/testing purposes
        WriteLn('current chunk');
        PrintArray(ref(xs[1]), 8);
        WriteLn('-----------');
      *)
      Add256(sigma, xs);
      HashStep(hs, xs, ctx);
    end;
    (* last block padding *)
    if (needpad <> 0) then 
    begin 
      imax := (8 - needpad);
      for j := 1 to imax do 
      begin 
        xs[j] := 0;
      end;
      for j := (imax + 1) to 8 do 
      begin 
        xs[j] := msg@;
        msg := succ(msg);
      end;
      (*
        only for debugging/testing purposes
        WriteLn('current chunk');
        PrintArray(ref(xs[1]), 8);
        WriteLn('-----------');
      *)
      Add256(sigma, xs);
      HashStep(hs, xs, ctx);
    end;
    (* adding length-hashing *)
    HashStep(hs, lenblk, ctx);
    (*
      only for debugging/testing purposes
      WriteLn('current chunk');
      PrintArray(ref(lenblk[1]), 8);
      WriteLn('-----------');
    *)
    (* adding chechsum-hashing *)
    HashStep(hs, sigma, ctx);
    (*
      only for debugging/testing purposes
      WriteLn('current chunk');
      PrintArray(ref(sigma[1]), 8);
      WriteLn('-----------');
    *)
    for i := 1 to 8 do 
    begin 
      res[i] := hs[i];
    end;
  end;
%
%
%
(* Testing all inner functions of Hash *)
  Procedure TestHash;
  var
    (* test message to be hashed and intermediate vals *)
    msg : Array[1..8] of UInt32;
    ss : Array[1..8] of UInt32;
    msg3 : Array[1..2] of UInt32;
    lin : Array[1..8] of UInt32;
    (* keys and its test values *)
    K1 : Array[1..8] of UInt32;
    K2 : Array[1..8] of UInt32;
    K3 : Array[1..8] of UInt32;
    K4 : Array[1..8] of UInt32;
    Ktest1 : Array[1..8] of UInt32;
    Ktest2 : Array[1..8] of UInt32;
    Ktest3 : Array[1..8] of UInt32;
    Ktest4 : Array[1..8] of UInt32;
    key : Array[1..8] of UInt32;
    (* some vals needed for test purposes *)
    hs : Array[1..8] of UInt32;
    i : Integer;
    total : Integer;
    ctx: TypeGostCtx;
    sigma : Array[1..8] of UInt32;
    sigmaexp : Array[1..8] of UInt32;
    tmp : Array[1..32] of UInt8;
    tmp2 : Array[1..16] of UInt16;
  begin 
    (* initial message to be hashed *)
    msg[1] := 1936028793;
    msg[2] := 1646277171;
    msg[3] := 1030255719;
    msg[4] := 1852140576;
    msg[5] := 744843105;
    msg[6] := 1936942445;
    msg[7] := 544434464;
    msg[8] := 1936287828;
    for i := 1 to 8 do 
    begin 
      sigma[i] := 0;
      sigmaexp[i] := msg[i];
    end;
    (* checksum to be used later *)
    Add256(sigma, msg);
    (* the test inner key value *)
    Ktest1[1] := 1933388832;
    Ktest1[2] := 1701340531;
    Ktest1[3] := 1953785705;
    Ktest1[4] := 2036818208;
    Ktest1[5] := 1651405683;
    Ktest1[6] := 543519593;
    Ktest1[7] := 845964648;
    Ktest1[8] := 857763156;
    Ktest2[1] := 286028605;
    Ktest2[2] := 219571560;
    Ktest2[3] := 319714420;
    Ktest2[4] := 104954215;
    Ktest2[5] := 486564462;
    Ktest2[6] := 370810981;
    Ktest2[7] := 151859820;
    Ktest2[8] := 1295594272;
    Ktest3[1] := 2159088115;
    Ktest3[2] := 1930293782;
    Ktest3[3] := 2231374833;
    Ktest3[4] := 3353475393;
    Ktest3[5] := 1644961279;
    Ktest3[6] := 985327898;
    Ktest3[7] := 1067518450;
    Ktest3[8] := 4111708729;
    Ktest4[1] := 2699198542;
    Ktest4[2] := 4279989234;
    Ktest4[3] := 3974265344;
    Ktest4[4] := 3887646689;
    Ktest4[5] := 3994903052;
    Ktest4[6] := 2886518202;
    Ktest4[7] := 2818883678;
    Ktest4[8] := 2710244076;
    (* starting values for key and hash token *)
    for i := 1 to 8 do 
    begin 
      hs[i] := 0;
      key[i] := 0;
    end;
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    WriteLn('GOST HASH test started');
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    WriteLn('Testing Packing/Unpacking');
    WriteLn('-----------------');
    (* here we pack / unpack 32 <-> 8 bit *)
    Unpack8(msg, tmp);
    Pack8(tmp, ss);
    total := 0;
    for i := 1 to 8 do 
    begin
      total := total + TestEquality(msg[i], ss[i]);
    end;
    (* here we pack / unpack 32 <-> 16 bit *)
    Unpack16(msg, tmp2);
    Pack16(tmp2, ss);
    for i := 1 to 8 do 
    begin
      total := total + TestEquality(msg[i], ss[i]);
    end;
    TestBattery(total, 16);
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    WriteLn('Testing Key Schedule');
    WriteLn('-----------------');
    Keygen(hs, msg, K1, K2, K3, K4);
    total := 0;
    for i := 1 to 8 do 
    begin
      total := total + TestEquality(K1[i], Ktest1[i]);
      total := total + TestEquality(K2[i], Ktest2[i]);
      total := total + TestEquality(K3[i], Ktest3[i]);
      total := total + TestEquality(K4[i], Ktest4[i]);
    end;
    TestBattery(total, 32);
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    WriteLn('Testing linear-step transformation');
    WriteLn('-----------------');
    (* the message after nonlinear step *)
    ss[1] := 3884319769;
    ss[2] := 220878381;
    ss[3] := 2369018009;
    ss[4] := 16715304;
    ss[5] := 1375988680;
    ss[6] := 1570492413;
    ss[7] := 1118551246;
    ss[8] := 851184411;
    (* the expected result after linear transform *)
    lin[1] := 3483012197;
    lin[2] := 1348036516;
    lin[3] := 1755331468;
    lin[4] := 1121875492;
    lin[5] := 3650896164;
    lin[6] := 2285741703;
    lin[7] := 1444707811;
    lin[8] := 857063476;
    LinearStep(hs, ss, msg);
    total := 0;
    for i := 1 to 8 do 
    begin 
      total := total + TestEquality(hs[i], lin[i])
    end;
    TestBattery(total, 8);
    (* 
        total := 0;
        InitGostCtx(ctx,key,s8,s7,s6,s5,s4,s3,s2,s1);
        Keygen(hs, msg, K1, K2, K3, K4);
        EncryptStep(hs, msg, ctx);
        for i := 1 to 8 do 
        begin 
          Write(' ');
          total := total + TestEquality(msg[i], ss[i]);
        end;
        TestBattery(total, 8); 
        Keygen(hs, msg, K1, K2, K3, K4);
        InitGostCtx(ctx,key,s8,s7,s6,s5,s4,s3,s2,s1);
        InitGostCtx(ctx,key,s1,s2,s3,s4,s5,s6,s7,s8);
        for i := 1 to 8 do 
        begin 
          K1[i] := K1[i];
        end;
        SetKey(ctx, K1);
        msg3[1] := 0;
        msg3[2] := 0;
        EncryptBlock(ctx, msg3);
        Write(' ');
        WriteLn(Swap(msg3[1]));
        Write(' ');
        WriteLn(Swap(msg3[2]));
        DecryptBlock(ctx, msg3);
        Write(' ');
        WriteLn(msg3[1]);
        Write(' ');
        WriteLn(msg3[2]);
    *)
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    WriteLn('Message length hashing test');
    (* intermediate keys *)
    Ktest1[1] := 3479755094;
    Ktest1[2] := 2594216988;
    Ktest1[3] := 2352693629;
    Ktest1[4] := 1703683299;
    Ktest1[5] := 1346537523;
    Ktest1[6] := 1507736853;
    Ktest1[7] := 1735829185;
    Ktest1[8] := 2753857332;
    Ktest2[1] := 2412734681;
    Ktest2[2] := 2157617308;
    Ktest2[3] := 1015823169;
    Ktest2[4] := 3345320996;
    Ktest2[5] := 3142599304;
    Ktest2[6] := 676978237;
    Ktest2[7] := 1717991078;
    Ktest2[8] := 3013878919;
    Ktest3[1] := 1316016023;
    Ktest3[2] := 1015047584;
    Ktest3[3] := 2235337924;
    Ktest3[4] := 1463327372;
    Ktest3[5] := 3401273533;
    Ktest3[6] := 3822560990;
    Ktest3[7] := 3516491656;
    Ktest3[8] := 1555258148;
    Ktest4[1] := 1481535695;
    Ktest4[2] := 3309076581;
    Ktest4[3] := 1216691340;
    Ktest4[4] := 374814874;
    Ktest4[5] := 3989486416;
    Ktest4[6] := 2028197798;
    Ktest4[7] := 4006713447;
    Ktest4[8] := 2136781659;
    (* the length of the message to be hashed *)
    for i := 1 to 7 do 
    begin 
      msg[i] := 0;
    end;
    msg[8] := 256;
    WriteLn('Testing Key Schedule');
    WriteLn('-----------------');
    Keygen(hs, msg, K1, K2, K3, K4);
    total := 0;
    for i := 1 to 8 do 
    begin
      total := total + TestEquality(K1[i], Ktest1[i]);
      total := total + TestEquality(K2[i], Ktest2[i]);
      total := total + TestEquality(K3[i], Ktest3[i]);
      total := total + TestEquality(K4[i], Ktest4[i]);
    end;
    TestBattery(total, 32);
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    (* message after encryption step *)
    ss[1] := 1723273054;
    ss[2] := 4049859681;
    ss[3] := 1183487272;
    ss[4] := 1641416083;
    ss[5] := 3857484343;
    ss[6] := 1070867065;
    ss[7] := 1020354605;
    ss[8] := 3715645062;
    (* the expected result after linear transform *)
    lin[1] := 728678963;
    lin[2] := 3351022052;
    lin[3] := 716973714;
    lin[4] := 1609200261;
    lin[5] := 3711453393;
    lin[6] := 3333200250;
    lin[7] := 620187179;
    lin[8] := 161722103;
    LinearStep(hs, ss, msg);
    total := 0;
    for i := 1 to 8 do 
    begin 
      total := total + TestEquality(hs[i], lin[i])
    end;
    TestBattery(total, 8);
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
     WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    WriteLn('Message checksum hashing test');
    (* intermediate keys *)
    Ktest1[1] := 1477964036;
    Ktest1[2] := 198466948;
    Ktest1[3] := 3058839335;
    Ktest1[4] := 1257615371;
    Ktest1[5] := 2771498362;
    Ktest1[6] := 2626674634;
    Ktest1[7] := 3139370182;
    Ktest1[8] := 3617920931;
    Ktest2[1] := 3894893024;
    Ktest2[2] := 3262699856;
    Ktest2[3] := 365711932;
    Ktest2[4] := 4235389878;
    Ktest2[5] := 3536272808;
    Ktest2[6] := 430361289;
    Ktest2[7] := 1048854773;
    Ktest2[8] := 3235755610;
    Ktest3[1] := 2001222361;
    Ktest3[2] := 4156726442;
    Ktest3[3] := 3943092695;
    Ktest3[4] := 2216413907;
    Ktest3[5] := 4223916704;
    Ktest3[6] := 2092258800;
    Ktest3[7] := 3566633088;
    Ktest3[8] := 178149052;
    Ktest4[1] := 2702539109;
    Ktest4[2] := 765443228;
    Ktest4[3] := 143424706;
    Ktest4[4] := 1190870482;
    Ktest4[5] := 1988406731;
    Ktest4[6] := 4199205382;
    Ktest4[7] := 1408235479;
    Ktest4[8] := 3228862216;
    (* CHECKSUM of the message to be hashed *)
    WriteLn('-----------------');
    WriteLn('checksum test');
    total := 0;
    for i := 1 to 8 do 
    begin 
      total := total + TestEquality(sigma[i], sigmaexp[i]);
      msg[i] := sigma[i];
    end;
    TestBattery(total, 8);
    WriteLn('---------------');
    WriteLn('Testing Key Schedule');
    WriteLn('-----------------');
    Keygen(hs, msg, K1, K2, K3, K4);
    total := 0;
    for i := 1 to 8 do 
    begin
      total := total + TestEquality(K1[i], Ktest1[i]);
      total := total + TestEquality(K2[i], Ktest2[i]);
      total := total + TestEquality(K3[i], Ktest3[i]);
      total := total + TestEquality(K4[i], Ktest4[i]);
    end;
    TestBattery(total, 32);
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    (* message after encryption step *)
    ss[1] := 720108150;
    ss[2] := 2824844669;
    ss[3] := 1863732713;
    ss[4] := 693216641;
    ss[5] := 3273552949;
    ss[6] := 1227947269;
    ss[7] := 529156418;
    ss[8] := 1426741293;
    (* the expected result after linear transform *)
    lin[1] := 4211029926;
    lin[2] := 363337321;
    lin[3] := 486489848;
    lin[4] := 3062669895;
    lin[5] := 3767870963;
    lin[6] := 2676038019;
    lin[7] := 783817077;
    lin[8] := 3546727601;
    LinearStep(hs, ss, msg);
    total := 0;
    for i := 1 to 8 do 
    begin 
      total := total + TestEquality(hs[i], lin[i])
    end;
    TestBattery(total, 8);
    WriteLn('-----------------');
    WriteLn(' ');
    WriteLn('-----------------');
    WriteLn('Test complete');
  end;
%
%
%
(* testing encryption of long arrays *)
  Procedure TestEncryptFile(ctx : TypeGostCtx);
  var 
    txt : Array[1..3] of UInt32;
    ctxt : Array[1..4] of UInt32;
    res : Array[1..3] of UInt32;
    i : Integer;
    total : Integer;
  begin 
    for i := 1 to 3 do 
    begin 
      txt[i] := 0;
      ctxt[i] := 0;
    end;
    WriteLn('Test Array Encryption');
    WriteLn('Encrypting Array of all zeros');
    WriteLn('using unique IV each time');
    WriteLn('Encryption result');
    EncryptCTR(ctx, ref(txt[1]), ref(ctxt[1]), 3);
    for i := 1 to 4 do 
    begin 
      Writeln(' ',ctxt[i]);
    end;
    WriteLn('------------');
    WriteLn('Decrypting Array');
    DecryptCTR(ctx, ref(ctxt[1]), ref(res[1]), 3);
    total := 0;
    for i := 1 to 3 do 
    begin 
      total := total + TestEquality(res[i], 0);
    end;
    TestBattery(total, 3);
  end;
%
%
%

(* testing encryption of long arrays *)
  Procedure TestPwd;
  var 
    ctx : TypeGostCtx;
    pwd : Array[1..20] of UInt32;
    res : Array[1..8] of UInt32;
    len : Integer;
    i : Integer;
  begin 
    Gost94Ctx(ctx);
    for i := 1 to 8 do 
    begin 
      res[i] := 0;
    end;
    for i := 1 to 20 do 
    begin 
      pwd[i] := i;
    end;
    WriteLn('Test Message Hashing');
    WriteLn('Full length hashing');
    HashMessage(ref(pwd[1]), 8, res);
    for i := 1 to 8 do 
    begin 
      WriteLn(' ', res[i]);
    end;
    WriteLn('Hashing with padding');
    for i := 1 to 8 do 
    begin 
      res[i] := 0;
    end;
    HashMessage(ref(pwd[1]), 17, res);
    for i := 1 to 8 do 
    begin 
      WriteLn(' ', res[i]);
    end;
  end;
%
%
%
    Procedure ReadPassword(var buf : Arg);
    begin 
        WriteLn;
        Pasred(buf);  
        If buf.inplen > 80 then  
        begin  
            WriteLn('Max length is 80 symbols!');  
            Goto 1;
        end; 
        If buf.inplen < 8 then  
        begin  
            WriteLn('Password cannot be less than 8 symbols');  
            Goto 1;
        end;
    end;
%
%
%
(* main program *)
  begin 
    (* test suite for encryption/hash stuff *)
    (* TestGost89(s8,s7,s6,s5,s4,s3,s2,s1); *)
    (* TestHash; *)
    (* testing encryption of long arrays with unfixed length *)
    (*
      for i := 1 to 8 do 
      begin 
        key[i] := 0;
      end;
      InitGostCtx(ctx, key, s8, s7, s6, s5, s4, s3, s2, s1);
      TestEncryptFile(ctx);
      WriteLn('-----------------');
    *)
    (* TestPwd; *)
    1:
    (* Reading a password *)
    (* maximal length of a string *)  
    buf.buflen := 140; 
    buf.inplen := 0; (* ОЧИCTKA *)  
    WriteLn; (* HУЖHО ДЛЯ PAБОTЫ ПPИГЛAШEHИЯ *)  
    (* BKЛ. CEKPETHЫЙ BBОД *)
    PASTEL[16] := PASTEL[16] + [10];
    WriteLn('Enter a password:   '); 
    ReadPassword(buf);
    (* Reading a password again *)
    tryval := 0;
    2:
    buf2.buflen := 140; 
    buf2.inplen := 0; (* ОЧИCTKA *)   
    WriteLn;
    WriteLn('Enter the password again:   '); 
    ReadPassword(buf2);
    if buf.inplen <> buf2.inplen then
    begin
        goto 3;
    end;
    eqcheck := 1;
    for i := 1 to buf.inplen do 
    begin 
        if (buf.a[i] <> buf2.a[i]) then 
        begin
            eqcheck := 0;
        end;
    end;
    if eqcheck <> 1 then  
    begin  
        3:
        WriteLn ('Passwords do not match!'); 
	    if (tryval < 3) then 
        begin
            tryval := tryval + 1;
		    goto 2;
		end;
        (* tryval >= 3 *)
        WriteLn('ТРОЕКРАТНАЯ ОШИБКА НЕСОВПАДЕНИЯ');
        goto 1;
    end;  
    WriteLn('Passwords are matched');  
    pwdlen := buf.inplen;
    for i:=1 to pwdlen do
    begin
        pwd[i] := Ord(buf.a[i]);
    end;
    (* only for debugging purposes 
        for i:=1 to pwdlen do
        begin
            Write(pwd[i]:2,' ');
        end;
    *)
    PASTEL[16] := PASTEL[16] - [10];
    WriteLn;
    (* obtain a key from a password *)
    HashMessage(ref(pwd[1]), pwdlen, key);
    InitGostCtx(ctx,key,s8,s7,s6,s5,s4,s3,s2,s1);
    (* entering a text message *)
    buf.BUFLEN := 140; (* ДЛИHA ARG.A *)  
    buf.INPLEN := 0; (* ОЧИCTKA *)  
    (*ВВОД ТЕКСТА ДЛЯ ЗАШИФРОВАНИЯ С ТЕРМИНАЛА *)
    WriteLn;
    WriteLn('ВВЕДИТЕ ТЕКСТ СООБЩЕНИЯ: ');
    (*СЧЕТЧИК ЦИКЛОВ СЧИТ. С ТЕРМИНАЛА. ДЛЯ ОТЛАДКИ *)
    k:=1;
    (*ОБЩИЙ СЧЕТЧИК СИМВОЛОВ. ДЛЯ ОТЛАДКИ *)
    m:=0;
    Rewrite(f);
  4:
    PASRED(buf);  
    if (buf.a[1]='к') and
      (buf.a[2]='о') and
      (buf.a[3]='н') and   
      (buf.a[4]='е') and  
      (buf.a[5]='ц') 
    then
      goto 5
    else
    begin
        k := k + 1;
        m := m + buf.inplen + 1;
        for i := 1 to buf.inplen do 
        begin
            Write(f, buf.a[i]);
        end;  
        WriteLn(f); (* ДЛЯ ПPABИЛЬHОГО ЗABEPШEHИЯ СТРОКИ *)  
        goto 4;
    end;
  5:
    WriteLn('-----------------');
    WriteLn('В файл были записаны следующие строки:');
    WriteLn('-----------------');
    Reset(f);
    While (Eof(f) <> true) do 
    begin
      Read(f, s);
      Write(s);
    end;
    WriteLn;
    Write('Общее число считанных символов');
    WriteLn(m);
    (* ENCRYPTING A FILE *)
    Reset(f);
    Rewrite(ctxt);
    EncryptMessage(ctx, f, ctxt);
    WriteLn('-----------------');
    WriteLn('Зашифрованный текст (численное представление)');
    WriteLn('-----------------');
    Reset(ctxt);
    While not Eof(ctxt) do 
    begin 
      Read(ctxt, j);
      WriteLn(j);
    end;
    (* Decrypting A FILE *)
    WriteLn('-----------------');
    WriteLn('Расшифрование сохраненного текста...');
    WriteLn('-----------------');
    Reset(ctxt);
    Rewrite(fres);
    DecryptMessage(ctx, ctxt, fres);
    Reset(fres);
    WriteLn('Расшифрованный текст');
    While (Eof(fres) <> true) do 
    begin
      Read(fres, s);
      Write(s);
    end;
end
.data 
    (* S-BOXES from GOST34.12-2015 *)
    s8:= 12,4,6,2,10,5,11,9,14,8,13,7,0,3,15,1;
    s7:= 6,8,2,3,9,10,5,12,1,14,4,7,11,13,0,15;
    s6:= 11,3,5,8,2,15,10,13,14,1,7,4,12,9,6,0;
    s5:= 12,8,2,1,13,4,15,6,7,0,10,5,3,14,9,11;
    s4:= 7,15,5,10,8,1,6,13,0,9,3,14,11,4,2,12;
    s3:= 5,13,15,6,9,2,12,10,11,7,8,1,4,3,14,0;
    s2:= 8,14,2,5,6,9,1,12,15,4,11,0,13,10,3,7;
    s1:= 1,7,14,13,0,5,8,3,4,15,10,6,9,12,11,2;
    (* S-BOXES from GOST94 test case *)
    sh1:= 1,15,13,0,5,7,10,4,9,2,3,14,6,11,8,12;
    sh2:= 13,11,4,1,3,15,5,9,0,10,14,7,6,8,2,12;
    sh3:= 4,11,10,0,7,2,1,13,3,6,8,5,9,12,15,14;
    sh4:= 6,12,7,1,5,15,13,8,4,10,9,14,0,3,11,2;
    sh5:= 7,13,10,1,0,8,9,15,14,4,6,12,11,2,5,3;
    sh6:= 5,8,1,13,10,3,4,2,14,15,12,7,6,0,9,11;
    sh7:= 14,11,4,12,6,13,15,10,2,3,8,1,0,7,5,9;
    sh8:= 4,10,9,2,13,8,0,14,6,11,1,12,7,15,5,3;
    (* *)
    magic := 7750000000000000C;
    mod31 := 2147483648;
    mod32 := 4294967296
end
*execute
*end file

``````
еконец

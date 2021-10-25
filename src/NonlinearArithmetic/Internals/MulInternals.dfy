// RUN: %dafny /compile:0 /noNLarith "%s" > "%t"
// RUN: %diff "%s.expect" "%t"

/*******************************************************************************
*  Original: Copyright (c) Microsoft Corporation
*  SPDX-License-Identifier: MIT
*  
*  Modifications and Extensions: Copyright by the contributors to the Dafny Project
*  SPDX-License-Identifier: MIT 
*******************************************************************************/

/* lemmas and functions in this file are used in the proofs in Mul.dfy */

include "GeneralInternals.dfy"
include "MulInternalsNonlinear.dfy"

module MulInternals {

  import opened GeneralInternals
  import opened MulInternalsNonlinear

  /* performs multiplication for positive integers using recursive addition */
  function method {:opaque} MulPos(x: int, y: int) : int
    requires x >= 0
  {
    if x == 0 then 0
    else y + MulPos(x - 1, y)
  }

  /* performs multiplication for both positive and negative integers */ 
  function method MulRecursive(x: int, y: int) : int
  {
    if x >= 0 then MulPos(x, y)
    else -1 * MulPos(-1 * x, y)
  }

  /* performs induction on multiplication */ 
  lemma LemmaMulInduction(f: int -> bool)
    requires f(0)
    /* Dafny selected triggers: {i + 1}, {i >= 0} */
    requires forall i {:trigger f(i), f(i + 1)} :: i >= 0 && f(i) ==> f(i + 1)
    /* Dafny selected triggers: {i - 1}, {i <= 0} */
    requires forall i {:trigger f(i), f(i - 1)} :: i <= 0 && f(i) ==> f(i - 1)
    ensures  forall i :: f(i)
  {
    forall i ensures f(i) { LemmaInductionHelper(1, f, i); }
  }

  /* proves that multiplication is always commutative */
  lemma LemmaMulCommutes()
    /* Dafny selected triggers: {x *y}, {y * x} */
    ensures  forall x:int, y:int {:trigger x * y} :: x * y == y * x
  {
    forall x:int, y:int
      ensures x * y == y * x
    {
      LemmaMulInduction(i => x * i == i * x);
    }
  }

  /* proves the distributive property of multiplication when multiplying an interger
  by (x +/- 1) */
  //rename for both directions ???
  lemma LemmaMulSuccessor()
    ensures forall x:int, y:int {:trigger (x + 1) * y} :: (x + 1) * y == x * y + y
    /* Dafny selected triggers: {x * y + y}, {(x + 1) * y} */
    ensures forall x:int, y:int {:trigger (x - 1) * y} :: (x - 1) * y == x * y - y
    /* Dafny selected triggers: {x * y - y}, {(x - 1) * y} */
  {
    LemmaMulCommutes();
    forall x:int, y:int
      ensures (x + 1) * y == x * y + y
      ensures (x - 1) * y == x * y - y
    {
      LemmaMulIsDistributiveAdd(y, x, 1);
      LemmaMulIsDistributiveAdd(y, x, -1);
    }
  }

  /* proves the distributive property of multiplication */
  lemma LemmaMulDistributes()
    /* Dafny selected triggers: {x * z + y * z}, {(x + y) * z} */
    ensures forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z
    /* Dafny selected triggers: {x * z - y * z}, {(x - y) * z} */
    ensures forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z
  {
    LemmaMulSuccessor();
    forall x:int, y:int, z:int
      ensures (x + y) * z == x * z + y * z
      ensures (x - y) * z == x * z - y * z
    {
      var f1 := i => (x + i) * z == x * z + i * z;
      var f2 := i => (x - i) * z == x * z - i * z;
      /* Dafny selects {x + i + 1}, {x + i + 1} for (x + i + 1) * z == (x + i + 1) * z
         and {x + 1} for (x + i + 1) * z == (x + i) * z + z.
         Dafny selects similar triggers for the next 4 lines. Removing these manual triggers results in verification time-outs. */
      assert forall i {:trigger (x + (i + 1)) * z} :: (x + (i + 1)) * z == ((x + i) + 1) * z == (x + i) * z + z;
      assert forall i {:trigger (x + (i - 1)) * z} :: (x + (i - 1)) * z == ((x + i) - 1) * z == (x + i) * z - z;
      assert forall i {:trigger (x - (i + 1)) * z} :: (x - (i + 1)) * z == ((x - i) - 1) * z == (x - i) * z - z;
      assert forall i {:trigger (x - (i - 1)) * z} :: (x - (i - 1)) * z == ((x - i) + 1) * z == (x - i) * z + z;
      LemmaMulInduction(f1);
      LemmaMulInduction(f2);
      assert f1(y);
      assert f2(y);
    }
  }

  /* groups distributive and associative properties of multiplication */
  predicate MulAuto()
  {
    /* Dafny selected triggers: {y * x}, {x * y} */
    && (forall x:int, y:int {:trigger x * y} :: x * y == y * x)
    /* Dafny selected triggers: {x * z + y * z}, {(x + y) * z} */
    && (forall x:int, y:int, z:int {:trigger (x + y) * z} :: (x + y) * z == x * z + y * z)
    /* Dafny selected triggers: {x * z - y * z}, {(x - y) * z} */
    && (forall x:int, y:int, z:int {:trigger (x - y) * z} :: (x - y) * z == x * z - y * z)
  }

  /* proves that MulAuto is valid */
  lemma LemmaMulAuto()
    ensures  MulAuto()
  {
    LemmaMulCommutes();
    LemmaMulDistributes();
  }

  /* performs auto induction for multiplication */
  lemma LemmaMulInductionAuto(x: int, f: int -> bool)
    requires MulAuto() ==> f(0)
                          && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1)) /* Dafny selected triggers: {i + 1}, {IsLe(0, i)} */
                          && (forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1)) /* Dafny selected triggers: {i - 1}, {IsLe(i, 0)} */
    ensures  MulAuto()
    ensures  f(x)
  {
    LemmaMulCommutes();
    LemmaMulDistributes();
    /* Dafny selected triggers: {i + 1}, {IsLe(0, i)} */
    assert forall i {:trigger f(i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
    /* Dafny selected triggers: {i - 1}, {IsLe(i, 0)} */
    assert forall i {:trigger f(i)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
    LemmaMulInduction(f);
    assert f(x);
  }

  /* performs auto induction on multiplication for all i s.t. f(i) exists */
  lemma LemmaMulInductionAutoForall(f: int -> bool)
    requires MulAuto() ==> f(0)
                          && (forall i {:trigger IsLe(0, i)} :: IsLe(0, i) && f(i) ==> f(i + 1)) /* Dafny selected triggers: {i + 1}, {IsLe(0, i)} */
                          && (forall i {:trigger IsLe(i, 0)} :: IsLe(i, 0) && f(i) ==> f(i - 1)) /* Dafny selected triggers: {i - 1}, {IsLe(i, 0)} */
    ensures  MulAuto()
    ensures  forall i :: f(i)
  {
    LemmaMulCommutes();
    LemmaMulDistributes();
    /* Dafny selected triggers: {i + 1}, {IsLe(0, i)} */
    assert forall i {:trigger f(i)} :: IsLe(0, i) && f(i) ==> f(i + 1);
    /* Dafny selected triggers: {i - 1}, {IsLe(i, 0)} */
    assert forall i {:trigger f(i)} :: IsLe(i, 0) && f(i) ==> f(i - 1);
    LemmaMulInduction(f);
  }

} 

-- rumur_flags: ['--smt-simplification', 'on'] + smt_args()
-- skip_reason: 'no SMT solver available' if len(smt_args()) == 0 else None

-- a version of smt-enum2.m using a typedef

type
  t: enum { A, B };

var
  x: t;
  y: boolean;

startstate begin
  y := true;
end;

rule begin
  -- if the SMT bridge can deal with enums, it should turn the following
  -- condition into `true`, avoiding a read of an undefined value from x
  if x = A | x = B then
    y := !y;
  end;
end;
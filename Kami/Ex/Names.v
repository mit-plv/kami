Require Import String.

Local Open Scope string.
Definition procRqValidReg := "procRqValid".
Definition procRqReplaceReg := "procRqReplace".
Definition procRqWaitReg := "procRqWait".
Definition procRqReg := "procRq".
Definition l1MissByState := "l1MissByState".
Definition l1MissByLine := "l1MissByLine".
Definition l1Hit := "l1Hit".
Definition writeback := "writeback".
Definition upgRq := "upgRq".
Definition upgRs := "upgRs".
Definition ld := "ld".
Definition st := "st".
Definition drop := "drop".
Definition pProcess := "pProcess".

Definition cRqValidReg := "cRqValid".
Definition cRqDirwReg := "cRqDirw".
Definition cRqReg := "cRqReg".
Definition missByState := "missByState".
Definition dwnRq := "dwnRq".
Definition dwnRs_wait := "dwnRs_wait".
Definition dwnRs_noWait := "dwnRs_noWait".
Definition deferred := "deferred".

Definition rqFromProc := "rqFromProc".
Definition rsToProc := "rsToProc".
Definition rqToParent := "rqToParent".
Definition rsToParent := "rsToParent".
Definition rqFromChild := "rqFromChild".
Definition rsFromChild := "rsFromChild".
Definition fromParent := "fromParent".
Definition toChild := "toChild".
Definition line := "line".
Definition tag := "tag".
Definition cs := "cs".
Definition mcs := "mcs".
Definition mline := "mline".

Definition elt := "elt".
Definition enqName := "enq".
Definition deqName := "deq".
Definition enqP := "enqP".
Definition deqP := "deqP".
Definition empty := "empty".
Definition full := "full".
Definition firstEltName := "firstElt".

Definition addr := "addr".
Definition data := "data".
Definition dataArray := "dataArray".
Definition read := "read".
Definition write := "write".

Definition rqFromCToPRule := "rqFromCToP".
Definition rsFromCToPRule := "rsFromCToP".
Definition fromPToCRule := "fromPToC".

Definition read0 := "read0".
Definition read1 := "read1".
Definition read2 := "read2".
Definition read3 := "read3".
Definition read4 := "read4".
Definition read5 := "read5".
Definition read6 := "read6".
Definition read7 := "read7".
Definition read8 := "read8".
Definition read9 := "read9".

Close Scope string.

#[global] Hint Unfold
     procRqValidReg procRqReplaceReg procRqWaitReg procRqReg
     l1MissByState l1MissByLine l1Hit writeback
     upgRq upgRs ld st drop pProcess

     cRqValidReg cRqDirwReg cRqReg missByState
     dwnRq dwnRs_wait dwnRs_noWait deferred

     rqFromProc rsToProc rqToParent rsToParent
     rqFromChild rsFromChild fromParent toChild
     line tag cs mcs mline

     elt enqName deqName enqP deqP empty full firstEltName

     addr data dataArray read write
     read0 read1 read2 read3 read4 read5 read6 read7 read8 read9

     rqFromCToPRule rsFromCToPRule fromPToCRule
  : NameDefs.


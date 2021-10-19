Require Import Model.Monad Model.MAL Core.Internal.
Import Bool Arith List List.ListNotations.

Definition checkChildOfCurrPart3 (currentPartition idPDchild : paddr) : LLI paddr :=
		perform isChildCurrPart := Internal.checkChildOfCurrPart currentPartition idPDchild in
		if negb isChildCurrPart
		then (* idPDchild is not a child partition, stop*) ret nullAddr
		else
		perform globalIdPDChild := readBlockStartFromBlockEntryAddr idPDchild in
		ret globalIdPDChild.
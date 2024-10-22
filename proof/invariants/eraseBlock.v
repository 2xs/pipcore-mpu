(*******************************************************************************)
(*  © Université de Lille, The Pip Development Team (2015-2021)                *)
(*                                                                             *)
(*  This software is a computer program whose purpose is to run a minimal,     *)
(*  hypervisor relying on proven properties such as memory isolation.          *)
(*                                                                             *)
(*  This software is governed by the CeCILL license under French law and       *)
(*  abiding by the rules of distribution of free software.  You can  use,      *)
(*  modify and/ or redistribute the software under the terms of the CeCILL     *)
(*  license as circulated by CEA, CNRS and INRIA at the following URL          *)
(*  "http://www.cecill.info".                                                  *)
(*                                                                             *)
(*  As a counterpart to the access to the source code and  rights to copy,     *)
(*  modify and redistribute granted by the license, users are provided only    *)
(*  with a limited warranty  and the software's author,  the holder of the     *)
(*  economic rights,  and the successive licensors  have only  limited         *)
(*  liability.                                                                 *)
(*                                                                             *)
(*  In this respect, the user's attention is drawn to the risks associated     *)
(*  with loading,  using,  modifying and/or developing or reproducing the      *)
(*  software by the user in light of its specific status of free software,     *)
(*  that may mean  that it is complicated to manipulate,  and  that  also      *)
(*  therefore means  that it is reserved for developers  and  experienced      *)
(*  professionals having in-depth computer knowledge. Users are therefore      *)
(*  encouraged to load and test the software's suitability as regards their    *)
(*  requirements in conditions enabling the security of their systems and/or   *)
(*  data to be ensured and,  more generally, to use and operate it in the      *)
(*  same conditions as regards security.                                       *)
(*                                                                             *)
(*  The fact that you are presently reading this means that you have had       *)
(*  knowledge of the CeCILL license and that you accept its terms.             *)
(*******************************************************************************)

Require Import Model.ADT Model.Monad Model.Lib Model.MALInternal.
Require Import Proof.WeakestPreconditions Proof.Consistency Proof.StateLib Proof.DependentTypeLemmas
              Proof.InternalLemmas Proof.Isolation.
Require Import Hoare Invariants.
Require Import FunctionalExtensionality List Lia Coq.Logic.ProofIrrelevance Coq.Bool.Bool Coq.Bool.BoolEq.
Import List.ListNotations.

Module WP := WeakestPreconditions.
Module DTL := DependentTypeLemmas.

Lemma eraseBlockAux timeout (startaddr curraddr endaddr: paddr) P:
{{ fun s => startaddr <= curraddr
            /\ startaddr < endaddr
            /\ curraddr < endaddr
            /\ timeout > curraddr - startaddr
            /\ (forall addr: paddr, addr > curraddr
                                    -> addr < endaddr
                                    -> lookup addr (memory s) beqAddr = None)
            /\ exists s0, P s0
                /\ currentPartition s = currentPartition s0
                /\ (forall addr: paddr, addr >= startaddr
                                        -> addr <= curraddr
                                        -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
                /\ (forall addr: paddr, ~In addr (getAllPaddrBlock startaddr endaddr)
                                        -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr) }}
MAL.eraseBlockAux timeout startaddr curraddr
{{ fun _ s => (forall addr: paddr, addr >= startaddr
                                    -> addr < endaddr
                                    -> lookup addr (memory s) beqAddr = None)
              /\ exists s0, P s0
                  /\ currentPartition s = currentPartition s0
                  /\ (forall addr: paddr, ~In addr (getAllPaddrBlock startaddr endaddr)
                                          -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr) }}.
Proof.
revert curraddr. induction timeout; simpl.
{
  intro. eapply weaken. apply WP.ret. simpl. intros s Hprops. exfalso.
  destruct Hprops as (_ & _ & _ & Hcontra & _). lia.
}
intro. eapply bindRev.
{ (* Monad.modify *)
  eapply weaken. apply modify. intros s Hprops. simpl.
  instantiate(1 := fun _ s => startaddr <= curraddr
                              /\ startaddr < endaddr
                              /\ curraddr < endaddr
                              /\ timeout >= curraddr - startaddr
                              /\ (forall addr : paddr, addr >= curraddr
                                                        -> addr < endaddr
                                                        -> lookup addr (memory s) beqAddr = None)
                              /\ (exists s0,
                                     P s0
                                     /\ currentPartition s = currentPartition s0
                                     /\ (forall addr : paddr,
                                          addr >= startaddr
                                          -> addr < curraddr
                                          -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
                                     /\ (forall addr: paddr,
                                           ~In addr (getAllPaddrBlock startaddr endaddr)
                                           -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr))).
  simpl. destruct Hprops as (HlebStartCurr & HltStartEnd & HlebCurrEnd & Htimeout & HremovedAddr & Hs0). split.
  assumption. split. assumption. split. assumption. split. lia.
  destruct Hs0 as [s0 (HP & Hcurr & HkeptAddrInside & HkeptAddr)]. split.
  - intros addr HgebAddrCurr HlebAddrEnd. destruct (beqAddr addr curraddr) eqn:HbeqAddrCurr.
    + rewrite <-DTL.beqAddrTrue in HbeqAddrCurr. subst addr. apply removeDupRemoved.
    + rewrite <-beqAddrFalse in HbeqAddrCurr. rewrite removeDupIdentity; try(assumption).
      assert(p addr <> p curraddr) by (apply DTL.paddrNeqNatNeqEquiv; assumption).
      apply HremovedAddr; try(lia).
  - exists s0. split. assumption. split. assumption. split.
    + intros addr HgebAddrStart HltAddrCurr.
      destruct (beqAddr addr curraddr) eqn:HbeqAddrCurr.
      {
        exfalso. rewrite <-DTL.beqAddrTrue in HbeqAddrCurr.
        assert(p addr = p curraddr) by (apply paddrEqNatEqEquiv; assumption). lia.
      }
      rewrite <-beqAddrFalse in HbeqAddrCurr. rewrite removeDupIdentity; try(assumption). apply HkeptAddrInside.
      assumption. assert(p addr <> p curraddr) by (apply DTL.paddrNeqNatNeqEquiv; assumption). lia.
    + intros addr HaddrNotInRange.
      destruct (beqAddr addr curraddr) eqn:HbeqAddrCurr.
      {
        rewrite <-DTL.beqAddrTrue in HbeqAddrCurr. subst addr. exfalso. contradict HaddrNotInRange.
        apply getAllPaddrBlockIncl; lia.
      }
      rewrite <-beqAddrFalse in HbeqAddrCurr. rewrite removeDupIdentity; try(assumption).
      apply HkeptAddr. assumption.
}
intro. destruct (beqAddr curraddr startaddr) eqn:HbeqCurrStart.
- rewrite <-DTL.beqAddrTrue in HbeqCurrStart. subst curraddr. eapply weaken. apply WP.ret. intros s Hprops.
  simpl. destruct Hprops as (_ & _ & _ & _ & HremovedAddr & Hs0).
  destruct Hs0 as [s0 (HP & Hcurr & _ & HkeptAddr)]. split. assumption. exists s0. split; try(split); assumption.
- rewrite <-beqAddrFalse in HbeqCurrStart.
  assert(HbeqCurrStartP: p curraddr <> p startaddr).
  { apply DTL.paddrNeqNatNeqEquiv; assumption. }
  eapply bindRev.
  { (* paddrPredM *)
    eapply weaken. apply Paddr.pred. intros s Hprops. simpl. split. apply Hprops. destruct Hprops as (Hres & _).
    lia.
  }
  intro predAddr. eapply weaken. apply IHtimeout. intros s Hprops. simpl.
  destruct Hprops as ((HlebStartCurr & HltStartEnd & HltCurrEndPlus & Htimeout & HremovedAddr & [s0 (HP & Hcurr &
      HleftAddr & HkeptAddr)]) & Hpred). unfold StateLib.Paddr.pred in Hpred.
  destruct (Compare_dec.gt_dec curraddr 0); try(exfalso; congruence). injection Hpred as Hpred.
  rewrite <-Hpred. simpl. split. lia. split. assumption. split. lia. split. lia. split.
  + intros addr HltAddrCurrMin HlebAddrEnd. apply HremovedAddr; lia.
  + exists s0. split. assumption. split. assumption. split; try(assumption). intros. apply HleftAddr; lia.
Qed.

Lemma eraseBlock (startaddr endaddr: paddr) P:
{{ fun s => P s }}
MAL.eraseBlock startaddr endaddr
{{ fun succeded s => exists s0, P s0
              /\ currentPartition s = currentPartition s0
              /\ (forall addr, In addr (getAllPaddrBlock startaddr endaddr)
                                -> lookup addr (memory s) beqAddr = None)
              /\ (forall addr, ~In addr (getAllPaddrBlock startaddr endaddr)
                                -> lookup addr (memory s) beqAddr = lookup addr (memory s0) beqAddr)
              /\ (succeded = false -> s = s0) }}.
Proof.
unfold MAL.eraseBlock. eapply bindRev.
{ (* Monad.ret *)
  eapply weaken. apply WP.ret. intros s Hprops.
  instantiate(1 := fun res s => P s /\ res = paddrLe endaddr startaddr). simpl. split. assumption.
  reflexivity.
}
intro isEndAddrBeforeStartAddr. destruct isEndAddrBeforeStartAddr.
- eapply weaken. apply WP.ret. intros s Hprops. simpl. exists s. destruct Hprops as (HP & HleEndStart).
  unfold paddrLe in HleEndStart. apply eq_sym in HleEndStart. apply PeanoNat.Nat.leb_le in HleEndStart.
  split. assumption. split. reflexivity. split.
  + intros addr Hcontra. exfalso. unfold getAllPaddrBlock in Hcontra.
    assert(Hsub: endaddr - startaddr = 0) by lia. rewrite Hsub in Hcontra. simpl in Hcontra. congruence.
  + split; intros; reflexivity.
- eapply bindRev.
  {
    eapply weaken. apply WP.Paddr.pred. intros s Hprops. simpl. destruct Hprops as (HP & HleEndStart).
    unfold paddrLe in HleEndStart. apply eq_sym in HleEndStart. apply PeanoNat.Nat.leb_gt in HleEndStart.
    split. lia. intro Hp.
    instantiate(1 := fun addr s => P s /\ startaddr < endaddr /\ endaddr - 1 = addr). simpl. split.
    assumption. split. assumption. reflexivity.
  }
  intro realEnd. eapply bindRev.
  {
    eapply weaken. apply eraseBlockAux. intros s Hprops. simpl. instantiate(1 := endaddr).
    destruct Hprops as (HP & HltStartEnd & Hpred). rewrite <-Hpred in *. split. lia. split. assumption. split.
    lia. split. unfold MAL.N. assert(endaddr <= maxAddr) by (apply Hp). lia. split.
    + intros addr HgtAddrEndMin HltAddrEnd. exfalso. lia.
    + exists s. split. instantiate(1 := fun s => P s /\ startaddr < endaddr /\ endaddr - 1 = realEnd). simpl.
      split. assumption. split; assumption. split. reflexivity. split; intros; reflexivity.
  }
  intro. eapply weaken. apply WP.ret. intros s Hprops. simpl.
  destruct Hprops as (HremovedAddr & [s0 ((HP & Hbounds & _) & Hcurr & HkeptAddr)]). exists s0. split. assumption.
  split. assumption. split; try(split); try(assumption); try(intro; exfalso; congruence).
  intros addr HaddrInBlock. apply getAllPaddrBlockInclRev in HaddrInBlock.
  destruct HaddrInBlock as (HleStartAddr & HltAddrEnd & _). apply HremovedAddr; lia.
Qed.

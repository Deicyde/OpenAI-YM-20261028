import YM.AnalyticNext.GRID_STOP_ATTENUATION.Primary.Manifest
import YM.MergeProof.ChaletS
import YM.MergeProof.North.Apiary
import YM.MergeProof.North.Sprite
import YM.MergeProof.North.Verve
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Stage.Iris
import YM.MultipleContact.Bunch.Focal
import YM.MultipleContact.Bunch.Dew
import YM.MultipleContact.Bunch.Gush
import YM.MultipleContact.Bunch.Sugary
import YM.MultipleContact.Bunch.Stained
import YM.MultipleContact.Bunch.Stator
import YM.MultipleContact.Bunch.Fermi
import YM.MultipleContact.Bunch.Corn
import YM.MultipleContact.Bunch.Lyme
import YM.MultipleContact.Bunch.Botan
import YM.MultipleContact.Bunch.Junction
import YM.MultipleContact.Bunch.Nigella
import YM.MultipleContact.Bunch.Buoy
import YM.MultipleContact.Bunch.Gild
import YM.MultipleContact.Bunch.Farr
import YM.MultipleContact.Bunch.Billow
import YM.MultipleContact.Bunch.Blot
import YM.MultipleContact.Bunch.Pond
import YM.MultipleContact.Bunch.Shan
import YM.MultipleContact.Bunch.SkyFall
import YM.MultipleContact.Bunch.Quark
import YM.MultipleContact.Bunch.Menu
import YM.MultipleContact.Bunch.Wraith
import YM.MultipleContact.Bunch.Thumb
import YM.MultipleContact.Bunch.Apiary

/- generalized from YM.MergeProof.North.Aeolus to arbitrary arity -/

set_option autoImplicit false
set_option linter.unusedSectionVars false
noncomputable section
namespace YM.MergeProof.BatchRibbons
variable {slot:Type}[Fintype slot][DecidableEq slot][Inhabited slot]
open Function Filter Lattice RG Pressure Wilson Finset MeasureTheory
open Push Marker Source Accent BatchRibbon Local Menu Extra.Histories Motion Merge PhysicalNext.Repeat Lotus
open Extra.Multi GridApprox.Nil
open Extra.Trajectories MergeProof.Float
open scoped Topology BigOperators Classical
section
variable {V : Type}[Fintype V][DecidableEq V]{G:Gauge}
variable (H:History G) {N m p k:ℕ}(u δ:ℕ→ℝ)(r:ℕ→ℕ)
    (D:∀ N p m:ℕ,m<N→GaugeDoor (H.rep N p (m+1)) (H.rep N p m))
variable (E:∀ m:ℕ,V→Site (H.S.side m p))(o:∀ m:ℕ,Name V slot→Site (H.S.side m p))(P:V→ Motion)(v:V)(w:ℕ→slot→ℝ)(B:V→Equiv.Perm V)
   (F:∀ m:ℕ,Name V slot→ Config G (H.S.side m p)→ℂ)(L:∀ m:ℕ,Name V slot→ℕ→ Config G (H.S.side m p)→ℂ)(a:Name V slot→ Config G (H.S.side N p)→ℂ)
set_option quotPrecheck false
local notation "Ξ"=> (Aged V slot)
local notation "f!"=> (fun i=> F i)
local notation "P'"=> H.levels.budget
local notation "ω"=> (fun i (j:Name V slot)=> w i j.2)
local notation "R"=> H.rep N p
local notation "Q"=> R N
variable (h:H.Selected) (h':Moonlit H r δ u D)(ht:Matchup H r δ p N k o (fun i (j:Name V slot)=> w i j.2) (Aged V slot))
    (hs:∀ (j:slot), Stately H u k N p (fun i=>o i (v,j)) (fun i=> w i j) (fun i=>F i (v,j)) (fun i=> L i (v,j)) (a (v,j)) D)
    (hP:∀ j,j≠v→B j v=j)(hV:∀ j,j≠v→∀ b:slot,a (j,b)=stepUp (P j) (E N j) (a (v,b)))
local notation "Ω"=> manifest H p N F L
local notation "y"=> tapes H p N L
variable (hM:∀ m:ℕ, k ≤ m→ m≤N→∀ i,Dominated (L m i)) (hT:∀ m:ℕ, k ≤ m→m≤N→∀ i,i≠v→∀ j:slot,F m (i,j)=stepUp (P i) (E m i) (F m (v,j))∧ tapes H p N L m (i,j)=floatUp (P i) (E m i) (tapes H p N L m (v,j))∧o m (i,j)=affine (P i).1 (E m i) (o m (v,j)))
include h h' ht hs hP hV hM hT
lemma penumbra (hk:k≤N) : Serves Q (F N) (y N) (birth Ξ Q a) v P (E N) B (o N) (ω N) (topPitch H N N) 1:=by
    have hA:= h.represents N p N le_rfl; have hε:= h'.endow N; have hp:=hA.vac; choose ψ t he hL hZ using fun j=>(hs j).patent
    let z(i:Name V slot):= if i.1=v then ψ i.2 else upwards (P i.1) (E N i.1) (ψ i.2)
    have hy(i:Name V slot): Attainment (Q).p (o N i) (z i) (t i.2):=by
       rcases i with ⟨i,j⟩; by_cases hi:i=v
       · subst i; simp only [z,if_true]; exact he j
       simp only [z,if_neg hi]; rw [(hT N hk le_rfl i hi j).2.2]; exact rise _ _ (he j)
    let E':ℝ:= (P' N).supportExponent-3; have hY:topPitch H N N=E':=by unfold topPitch; rw [if_pos rfl]
    obtain ⟨hc,hY',hψ,hI⟩:=hε
    let π i:= (hA.good.labels.moves (P i).1 (E N i)).some
    let c:= H.levels.clock.forcedAllowance N; have h1 : (((Q).p.B+(Q).p.B+1:ℕ):ℝ)^4*(c+r N*siteFactor (Q).p.B*u N) ≤ (Q).p.supportExponent - E':=by rw [hp]; exact hψ.trans_eq (by unfold E'; ring)
    refine (hY.symm ▸ spawn hA.good.labels z (cloth hy (fun i=>hL i.2) (fun i=>ht.pos N hk le_rfl i|>.le)) (by intro i hi;simp [z,hi]) hP (fun i=>⟨π i⟩) (ht.occ N hk le_rfl) hc (ht.pos N hk le_rfl) le_rfl hY' h1 (by rw [hp]; exact hI) (fun U=>(Tour.bright H h N p _ le_rfl U).ne') zero_le_one (hM N hk le_rfl) ?_ ?_)
    · rintro ⟨i,j⟩; by_cases hi:i=v
      · subst i; simp only [z,if_true]; exact hZ j
      change hook _ _ (z (i,j))=y N (i,j); simp only [z,if_neg hi]; rw [hooked (P i) (E N i) (π i), (hT N hk le_rfl i hi j).2.1]; exact congr_arg _ (hZ j)
    rintro ⟨i,j⟩ U; by_cases hi:i=v
    · subst i; exact (hs j).writes U
    have he':= opals (P i) H h le_rfl (E N i) (F N (v,j)) (π i) (hM N hk le_rfl _) (hM N hk le_rfl _) (hT N hk le_rfl i hi j|>.2.1)
    rw [hV i hi, (hT N hk le_rfl i hi j).1, he']; simp only [stepUp,← (hs j).writes,scalar_mul, Motion.scalar_real]; rw [WardBin.Wheels.rep_spins (P i).1 h le_rfl]
end
end YM.MergeProof.BatchRibbons

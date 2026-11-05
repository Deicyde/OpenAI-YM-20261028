import YM.AnalyticNext.CONNECTED_LOG_IDENTITY.Projection
import YM.PhysicalNext.RG_NEXT_COMPLETE_REPEATABLE_NONLINEAR_STEP.Deck.Primer
/-! # Pull full Path clamps on covers. T reference aligns. -/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.Repeat.Deck
open Function Filter Lattice RG Pressure Tree Wilson Finset
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Work.E03
open ConnectedActivityE6 Channel Oriented SliceRows Control Window Coat DataKernel
open Further.PhysicalPeriodLimitF933 Macrame Bloch Laurent
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f C F: Side} {P : Patch} {M : ℕ}
section neat
variable (h : c.val ∣ C.val) (hh : C.val=c.val*M) (W : Config G c)
local notation "X" => normal h hh
local notation "q" => (Macrame.splitter h)
include h hh
lemma mirror (i:Cell C): faceValue ((X).links W) i = faceValue W (curr (q) i):= (X).traveller ..
variable (R : PathData G) (p:Clip) (i k:ℕ) {t:ℝ}
lemma fasces (s : Twin C) : Pressure.plotted R p i k ((X).links W) s=plotted R p i k W (dip (q) s):= by
  unfold plotted; change (if s.2 then _ else _) = (if s.2 then _ else _); split
  · apply tsum_congr; intro j
    unfold shortenTerm; change (if (R.row s.1.2 j).2.length*k ≤ i then _ else 0) = (if (R.row s.1.2 j).2.length*k ≤ i then _ else _); split
    · unfold PathData.ellTerms Slot.atSite; rw [(X).expansion]; rfl
    rfl
  unfold shoot; rw [mirror]; rfl
lemma shot (he : 0 ≤ t) (i : Site C) : PathData.kept p t i ((X).links W) ↔ PathData.kept p t (Macrame.splitter h i) W := by
  constructor
  · intro H j; let f := rise h i j.1
    have hp: curr (q) (f,j.2)=j:=Prod.ext (dawns ..) rfl
    convert H (f,j.2) using 2
    · rw [mirror h, hp]
    rw [show separation i f=_ from climb h ..]
  intro H j; have ht:= H (curr (q) j); rw [mirror]; refine le_trans ht (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (div_le_div_of_nonneg_right (by exact_mod_cast less h i j.1) p.radius_pos.le)) he)
lemma volt (he:0 ≤ t) (u:Twin C) : Pressure.thinned R p t k i ((X).links W) u=Pressure.thinned R p t k i W (dip (q) u):= by
  have hf:= shot h hh W p he u.1.1; have hs:= fasces h hh W R p i k u
  unfold Pressure.thinned; simp only [dip,Prod.map_fst,Prod.map_snd,id_eq,curr] at hf hs ⊢; split
  · unfold Pressure.plotted at hs; rw [hf]; split; · split at hs <;> grind
    rfl
  unfold shoot Pressure.toll; rw [mirror]
end neat
section gather
variable {h : f.val=c.val*P.L.val} {H : F.val=C.val*P.L.val} {Q:KernelChoices} (hC : C.val=c.val*M) (he:2 ≤ c.val)
local notation "L" => Lace.project (h:=h) (H:=H) hC he
local notation "S" => stepped Q h
local notation "Y" => stepped Q H
variable (V: Config G c) {T:Tube G (stepped Q h)} {A: Tube G (stepped Q H)} {Pt:Teller G} (hp:A=re T) (h': Pt.Funds (stepped Q h) T) (hY : Pt.Funds (stepped Q H) A) {o:ℕ} (hv:2*o<c.val)
include hC he hp
lemma vele (t:Config G f) (i k:ℕ) (p: Twin F) : Pressure.plotted A.up A.high i k ((L).high.links t) p=plotted T.up T.high i k t (dip (L).high.cut p):= by
  subst A; exact fasces (c:=f) (C:=F) (show f.val∣F.val from ⟨M,by nth_rw 1 [H]; rw [hC,h]; ac_rfl⟩) (show F.val=f.val*M from (by rw [H,h,hC]; ac_rfl)) ..
include hv h' hY
lemma whistle : let _m := T.R; let f:= (decreed H).parent; let f':=(decreed h).parent; let _U i:= V i
    Nary (divides hC) (dip (L).high.cut) (dip (L).low.cut) (fun i=> f i.1.1) (fun i=> i.1.1) (fun i=> f' i.1.1) (fun i=> i.1.1)
     (Tube.Φ A o ((L).low.links V)) (T.Φ o V) o ∧ Nary (divides hC) (curr (L).low.cut) (dip (L).low.cut) Prod.fst (fun i=>i.1.1) Prod.fst (fun i=>i.1.1)
     (Tube.Φ' A o ((L).low.links V)) (T.Φ' o V) o ∧ Nary (divides hC) (curr (L).low.cut) (dip (L).low.cut) Prod.fst (fun i=>i.1.1) Prod.fst (fun i=>i.1.1)
     (Tube.N A o ((L).low.links V)) (T.N o V) o:= by
  intro r f f' U; subst A; let p:= L
  have hx:= onfloor (h:=h) (H:=H) hC he; have hl:= hx.pr (E:=PlaqAxes)|>.pr (E:=Bool)
  let T':Tube G (stepped Q H):=re T
  refine ⟨⟨footing (h:=h) (H:=H) hC he|>.pr|>.pr,hl,hv, upfrom (X:=re T) hC he rfl hv V,(crosses _ T' Pt hY).reach _,(crosses _ T Pt h').reach _⟩,⟨hx.pr,hl,hv,fun i j h=>?_,?_,?_⟩,⟨hx.pr,hl,hv,fun i j h=>?_,?_,?_⟩⟩
  · exact crane hC V hv T.R.mn P.L.property (pole i) (mesh j) h
  · exact (sameLevel o P.L.val P.L.property T'.R.mn (Row.rights _ _ hY.crosses.1 Pt.width.le) pole mesh).reach ((L).low.links V)
  · exact (sameLevel o P.L.val P.L.property T.R.mn (Row.rights _ _ h'.crosses.1 Pt.width.le) pole mesh).reach V
  · exact crane hC V hv T.R.o P.L.property i (mesh j) h
  · exact (sameLevel o P.L.val P.L.property T'.R.o (Row.rights _ _ hY.crosses.2.1 Pt.width.le) id mesh).reach ((L).low.links V) -- check projection
  exact (sameLevel o P.L.val P.L.property T.R.o (Row.rights _ _ h'.crosses.2.1 Pt.width.le) id mesh).reach V
end gather
end YM.PhysicalNext.Repeat.Deck

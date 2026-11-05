import YM.RG05Readout.Address.Horizon
import YM.RG05Readout.Offsets.Null
import YM.MergeProof.Volumes

/-!
# Retiring field degrees in an output with increased test degree

Change REAL one-mark presentation with exactly the same density and a new
attaching merger ticket. Cost on regular and forced data at the adopted
powers. These are inputs afterwards to `Tale` in aggregating copies. No
adjoining an arbitrary null-germ vector to a physical multisource rep.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG05Readout.Address
open Function Filter Set MeasureTheory Lattice Wilson Labels RG Source Extra.Histories Bid
open Push Local Planned.GuardedAtom Guard YM.MergeProof Extra.Histories.Relay
open scoped Topology ContDiff BigOperators Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{d e k:ℕ} {T:Labels.Frame G e} {F:Labels.Frame G d}
open Next.Foundations Drops
variable (Y : Hol G) (o:Site n) (B:SectionData F) (Z:SectionData T) (R: RG.Rep G n) (x:F.Coeff)
variable (v w:ℝ)
def upgradeCost (p : ℝ) := factor Y Z p w * (Real.exp ((p+2)*atomTiles B) * v)
-- primal portion laid out in Raw of lower horizon.
def primaryAdvance (T : Labels.Frame G e) : Push.Local.Raw T n where
    seed := (x 0) • T.e0
    bulk := fun i=> if i=0 then presented B o R.p.threshold (F.core x) else 0
    forced := 0
local notation "V" => primaryAdvance o B R x T
local notation "X" => B.footprint o
local notation "S0"=> Real.exp ((R.p.supportExponent+2)*atomTiles B)
section
variable {v w R} (hr:Readable Y B R.p n v) (he:Readable Y Z R.p n w)
include hr he
omit he in
lemma one_price (t:ℝ) :
    (V).Format o (fun _=>X) R∧ Planned.GuardedAtom.Deck V o (fun _=>X) R t (S0*v*F.coeffSize x) 0 :=by
    let f:= primaryAdvance o B R x T
    obtain ⟨hZ,ha⟩:= presented_good o hr (F.core x)
    have hx:=presented_good o hr 0; rw [map_zero, show F.coeffSize 0=0 from (by simpa only [zero_smul, norm_zero] using axis_cost F 0 0)] at hx -- wrong
    have hQ:= hr.nonneg
    have hB : ∃ p, f.cost o (fun _=>X) R.p p ∧ SumBudget (fun i=> reservedMass R.p X (p i)) (S0*v* F.coeffSize x):=by
       let p(i:ℕ):= if i=0 then v*F.coeffSize (F.core x) else 0
       have ht i : R.p.supBounds o X (f.bulk i) (p i):=by
          by_cases hi:i=0
          · unfold f primaryAdvance p; simpa only [if_pos hi]
          simp only [f,primaryAdvance,p,if_neg hi]; simpa only [mul_zero] using hx.2
       let B' (i:ℕ):=reservedMass R.p X (p i); have hv i (hi:i≠0): B' i=0:=by unfold B' p reservedMass; rw [if_neg hi,mul_zero]
       have hz i:0 ≤ B' i:=mul_nonneg (Real.exp_pos _).le (ht i|>.1)
       refine ⟨p,ht,hz,summable_of_ne_finset_zero (s:={0}) (fun i hi=>hv i (by simpa using hi)),?_⟩
       rw [tsum_eq_single (0:ℕ) hv]; unfold B' p reservedMass; rw [if_pos rfl,mul_assoc]
       exact mul_le_mul (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (by exact_mod_cast atomTiles_price B R.p o) (add_nonneg R.p.exponent_pos.le zero_le_two))) (mul_le_mul_of_nonneg_left (Work.G08.size_core F x) hQ) (mul_nonneg hQ (Work.G08.size_nonneg ..)) (Real.exp_pos _).le
    refine ⟨⟨fun _=>Finset.mem_image.mpr ⟨0,hr.sound.anchored,by simp⟩,fun i=>?_,?_⟩, ⟨hB,?_⟩⟩
    · simp only [primaryAdvance]; split; exact hZ; exact hx.1
    · exact ⟨fun _ _ h=> (h rfl).elim,fun _ h=>(h rfl).elim,fun _ _ _=>rfl, fun _ _ _ _ _=>rfl,fun _=>measurable_const⟩
    exact ⟨0,by simp [SumBudget,BudgetPoint.mass],by simp [primaryAdvance]⟩
omit he hr in
lemma unit_at (T : Labels.Frame G e) (D:SectionData T) : primary D o R.p.threshold T.e0=1:=by
    funext i; have h0 : T.core T.e0=0:=by
       funext j; by_cases h:j=0<;>simp [h,Frame.core,Frame.e0]
    change T.e0 0 + maskLinear _ _ (presented D o R.p.threshold (T.core T.e0)) i=1
    rw [h0,map_zero,map_zero,show T.e0 0=1 from Pi.single_eq_same ..]; exact add_zero _
omit he hr in
lemma primary_bill :
    Push.Local.Raw.eval (V) o (fun _=>X) Z R = fun U=> (R.eval U:ℂ)* Local.primary B o R.p.threshold x U :=by
    let f:Push.Local.Raw T n:=V
    have hp': Local.primary Z o R.p.threshold f.seed=(x 0) • 1:=by rw [show f.seed=x 0 • T.e0 from rfl,map_smul,unit_at]
    funext U; unfold Push.Local.Raw.eval
    have hr j (h:j≠0): masked R.p.threshold X ((V).bulk j) U=0:=by
       simp only [primaryAdvance,if_neg h]; exact congr_fun (map_zero (maskLinear _ _)) _
    -- rectify ambiguous local
    rw [tsum_eq_single 0 hr,hp']
    simp only [show (V).forced=0 from rfl,map_zero,tsum_zero,mul_zero,add_zero,Pi.smul_apply, Pi.one_apply,smul_eq_mul,mul_one]
    change (_:ℂ)= _*(x 0 + (masked R.p.threshold X (presented B o R.p.threshold (F.core x)) U))
    congr
omit he hr in
private lemma weighted_round (hz:e ≤ d) (f:Config G n→ℂ){p:BudgetPoint}(hf:p.Regular X f)(hh:d ≤ p.order)(J:Probe G e):
    runProbe T J (weighted Y T o X p.threshold f)=runProbe F (reduced e J.1,⟨J.2.val,lt_of_lt_of_le J.2.isLt (Nat.add_le_add_right hz 1)⟩) (weighted Y F o X p.threshold f):=by
    rw [← sample_eq T Y o _ hf (hz.trans hh),← sample_eq F Y o _ hf hh]
    unfold sample; dsimp only; split_ifs <;> try rfl
    rw [← prune_smul,prune_test Y hz]
omit he hr in
lemma unit_round (z:e≤d)(J:Probe G e) : runProbe T J T.e0=runProbe F (reduced e J.1,⟨J.2.val,lt_of_lt_of_le J.2.isLt (Nat.add_le_add_right z 1)⟩) F.e0:=by
    rw [← T.coords_unit, ← F.coords_unit,runProbe_eq,runProbe_eq,LinearEquiv.symm_apply_apply,LinearEquiv.symm_apply_apply]; simp [Labels.unit]
omit he in
lemma primary_coordinates (h:e ≤ d) (S: Guard.Keeper R.p R.activities)
    (J: Probe G e) : runProbe T J (mint (S.supply fun _:ℕ=> Local.joint Z o X) (V) Y).x= runProbe F (reduced e J.1,⟨J.2.val,lt_of_lt_of_le J.2.isLt (Nat.add_le_add_right h 1)⟩) x:=by
    let u:= primaryAdvance o B R x T; let r:=R.p.threshold; let g := presented B o r (F.core x)
    let Ψ := mint (S.supply fun _ : ℕ=> Local.joint Z o X) u Y
    let A (i):=u.row o (fun _=>X) Y r i; have ha i (hi:i ≠ 0): A i=0:=by simp [A, Push.Local.Raw.row,u,primaryAdvance,hi,weighted]
    have hM : Ψ.x=u.seed+A 0:=by change u.seed+(∑' i,A i)=_; rw [tsum_eq_single 0 ha]
    let p: Probe G d:=(reduced e J.1,⟨J.2.val,lt_of_lt_of_le J.2.isLt (Nat.add_le_add_right h 1)⟩)
    have hψ:weighted Y F o X r g=F.core x:=by
       unfold weighted; rw [project_eq (p:=(F.coords.symm (F.scaled r⁻¹ (F.core x)))) (f:=g) (placed_reads B o hr.fit hr.sound (F.scaled r⁻¹ (F.core x))),LinearEquiv.apply_symm_apply,F.scaled_inv]; exact R.p.threshold_pos.ne'
    have hK (i:ℂ) (D:Probe G d): runProbe F D (i • F.e0 + F.core x)=i • runProbe F D F.e0 + runProbe F D (F.core x):= by rw [map_add,map_smul]
    change runProbe T J Ψ.x = runProbe F p x
    rw [hM,map_add,show u.seed=(x 0) • T.e0 from rfl,map_smul,unit_round (F:=F) h,show A 0=weighted Y T o X r g from rfl, weighted_round Y o B h g (presented_good o hr (F.core x)).1 hr.order J,hψ,← hK]
    rw [← core_split F x]
end
-- include prices at coarser halo
section
variable {R Y v w} {C Q k ξ g s c :ℝ} {o}
lemma rewrite_down (h:e≤d)(U:Coefficient F n)(S:Keeper R.p R.activities)(hs: U.Format o Y R)(ht:U.remBound o R (Real.sqrt s) k)
    (hh:Readable Y B R.p n v)(ha:Readable Y Z R.p n w)(hr:R.Lawful ξ C Q g s) (hp:0<s)(hg: hitWidth R.p * Real.sqrt s≤1) :
    let A:=upgradeCost Y B Z v w R.p.supportExponent *F.coeffSize U.x
    ∃ Vv: Coefficient T n,Vv.Format o Y R∧ Vv.density o Z R=U.density o B R∧
        Vv.remBound o R (Real.sqrt s) (A+(0+A)+k) ∧
        (∃ κ, profile R.activities Vv.forced= profile R.activities U.forced+hook R.activities R.p.threshold κ ∧ Attainment R.p o κ A) ∧
        ∀ J:Probe G e,runProbe T J Vv.x=runProbe F (reduced e J.1,⟨J.2.val,lt_of_lt_of_le J.2.isLt (Nat.add_le_add_right h 1)⟩) U.x:=by
    intro A'; let r:=primaryAdvance o B R U.x T
    let R' := S.supply (fun _ : ℕ=>Local.joint Z o X)
    obtain ⟨hA,hA'⟩:= one_price (T:=T) Y o B U.x hh (Real.sqrt s)
    let P:= mint R' r Y; let c₀:=factor Y Z R.p.supportExponent w
    have hC:A'=c₀*(S0*v*F.coeffSize U.x):=by unfold A' upgradeCost c₀; ring
    have hV:=vigor (M:=r) hA' hA ha; have hP: Tare r o (fun _=> X) Y Z R w s (Real.sqrt s) A' 0 A':=by rw [hC]; exact Deck.usual (h:=hA') hp hg ha hA
    rw [← hC] at hV
    have h0:= Real.sqrt_pos.mpr hp
    obtain h₁:=tab_mint R' hA hr h0 ha hP; have hδ: P.Format o Y R:=usage R' hA hr ha
    let t:Coefficient T n:= {x:=0,support:=U.support,regular:=U.regular,forced:=U.forced}
    have ht': t.Format o Y R:= ⟨hs.smooth,hs.origin,hs.identity_null,fun i hh=>prune_vanish h (hs.projects i hh),hs.forcing,hs.carried,hs.invariant,hs.supported,hs.borel⟩
    have ht0: t.remBound o R (Real.sqrt s) k:= ht; let P':=beside P t
    have he:=h₁.bound le_rfl
    obtain ⟨h₂,h₃⟩:= presentation hδ he ht' ht0
    refine ⟨P',h₂,?_,h₃,⟨_,?_,hV⟩,fun p=>?_⟩
    · unfold P'; rw [plus hr he ht0]; rw [show P.density o Z R=_ from (value_mint R' hA hr h0 ha hP).trans (primary_bill o B Z U.x)]
      funext Vv; unfold Coefficient.density; simp only [Pi.add_apply]; change _+(↑(R.eval Vv)*((Local.primary Z o R.p.threshold t.x Vv)+(∑' i,t.maskedTerm R i Vv))+_)=↑(R.eval Vv)*((Local.primary B o R.p.threshold U.x Vv)+(∑' i,t.maskedTerm R i Vv))+_
      rw [show t.x=0 from rfl,map_zero,Pi.zero_apply,zero_add,mul_add]; rw [add_assoc];rfl
    · unfold P'; rw [duo_profile he ht0]; rw [show profile R.activities P.forced=profile R.activities r.forced+hook R.activities R.p.threshold (coda Z Y o (fun _=> X) r R) from budgetProfile R' hP hA ha hr h0,show profile R.activities r.forced=0 from funext (fun i=> funext (fun U=>by simp [profile,r,cram,primaryAdvance])),zero_add,add_comm]
    unfold P'; rw [reckon,show t.x=0 from rfl,add_zero]; exact primary_coordinates Y o B Z U.x hh h S p
end
end YM.RG05Readout.Address

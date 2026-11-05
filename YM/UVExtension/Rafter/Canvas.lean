import YM.UVExtension.Rafter.Bait
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Rafter
open Function Filter Lattice Wilson MeasureTheory RG Push Push.AbsoluteSums
open Lamppost Concert Local MergeProof Planned.GuardedAtom Guard Rainfall Eyelet Source Next.Foundations Wet Extra.Histories
open scoped BigOperators Topology ContDiff Classical Matrix.Norms.Frobenius
variable {G:Gauge}{n:Side}{d:ℕ}{ι D Z E:Type} [NormedAddCommGroup Z][NormedSpace ℂ Z]
    {T:Opening D Z}{A:Hol G}{U:Labels.Frame G d}{B:SectionData U}
open Topology Set BoundedContinuousFunction
variable {p:BudgetPoint} {t a b w:ℝ} (V:D→ Roc d A n p)(X:ℕ→Support n)(M:D→ℕ→ Config G n→ℂ)
-- rerouting residual observations
local notation "Λ"=> joint B (0:Site n) ∘ X
variable (he:∀ i, (0:Site n)∈joint B 0 (X i))
-- avoid dependant HEq.Tune.
local notation "P"=> shop (G:=G) p (joint B (0:Site n) ∘ X)
local notation "H"=> fun u i k=> Tap.read k (Local.residual A B 0 (X i) p.threshold (M u i))
include he
variable (hA: Stalk (shop (G:=G) p (joint B 0 ∘ X)) T (fun u i (k:Tap p G 0 (joint B 0 (X i)))=> Tap.read k (Local.residual A B 0 (X i) p.threshold (M u i))) a)
variable (hw:∀ u (i:Eyelet.Slot n) k,gaze d A p i k (V u)= (Eyelet.fee p i.1.val:ℂ)*k.read (if i.1.val= joint B 0 (X i.2) then Local.residual A B 0 (X i.2) p.threshold (M u i.2) else 0))
include hw hA
lemma larboard (ha:0≤ a):∃ g:Z→Roc d A n p, Bumps T.span g ∧ (∀ d,g (T.call d)= V d)∧∀ z∈ T.span, ‖g z‖ ≤ 2*1*a:=by
    let y(i:ℕ):= joint B 0 (X i); let e:ℕ↪ Eyelet.Slot n:=⟨fun i=> (⟨y i, he i⟩,i),fun a b h=>congr_arg Prod.snd h⟩
    apply sprigs hA ha zero_le_one; intro S v c hc hM
    obtain ⟨f,hf,hX⟩:=hM.afloat; rw [one_mul]; let x:=∑ i∈S,v i • V i; have ht : HasSum (fun i=> ‖x i‖) ‖x‖:= castL x
    have hv(i k): gaze d A p i k x= ∑ j∈S,v j*((Eyelet.fee p i.1.val:ℂ)*k.read (if i.1.val=y i.2 then Local.residual A B 0 (X i.2) p.threshold (M j i.2) else 0)):=by unfold x; rw [map_sum]; simp_rw [map_smul, hw]; rfl
    refine ht.tsum_eq.symm.trans_le ((show SumBudget (fun i=> ‖x i‖) c from Local.sumBudget_pass e _ ?_ ?_).2.2)
    · let P':=shop (G:=G) p y; refine budget_mono (hX ()) (fun i=>norm_nonneg _) fun i=>?_
      have h(i k): gaze d A p (e i) k x = (Eyelet.fee p (y i):ℂ)*∑ j∈S,v j*k.read (Local.residual A B 0 (X i) p.threshold (M j i)):=by
          rw [hv]; change ∑ j∈S,v j*((Eyelet.fee p (y i):ℂ)*k.read (if y i=y i then Local.residual A B 0 (X i) p.threshold (M j i) else 0))= _; simp only [if_true, Finset.mul_sum]; exact Finset.sum_congr rfl fun j _=> mul_left_comm ..
      have hz:(P').cost () i≥ Eyelet.fee p (y i):= Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (by linarith) (Nat.cast_nonneg _))
      apply le_trans _ (mul_le_mul_of_nonneg_right hz ((hf i).1)); refine (BoundedContinuousFunction.norm_le (mul_nonneg (Eyelet.toll_pos ..|>.le) ((hf i).1))).2 fun j=>?_
      change ‖gaze d A p (e i) j x‖ ≤ _; rw [h,norm_mul,Complex.norm_real,Real.norm_of_nonneg (Eyelet.toll_pos ..|>.le)]; exact mul_le_mul_of_nonneg_left ((hf i).2 j) (Eyelet.toll_pos ..|>.le)
    intro i hi; apply norm_eq_zero.mpr; apply Gondola.ext (p:=p) i; intro k; have ht :i.1.val ≠ joint B 0 (X i.2):= fun h=> hi ⟨i.2, Prod.ext (Subtype.ext h.symm) rfl⟩
    change gaze d A p i k x = _; rw [hv,map_zero]; simp [y,ht,Tap.read,show (0:Config G n→ℂ)=(fun _=>0) from rfl,Work.G07.left_const]

omit he hw hA
variable (f: D→ Res G n)(Y:D→ Coil G n p)
lemma sails (hv: Stalk (boxGoal G n p) T f a)(hr:∀ d (i:StockTag n) t, tire p i t (Y d)= ((Eyelet.fee p i.val.1 / w:ℝ):ℂ)* f d i.val t.tag)(hp:0<w)(ha:0≤a): ∃ g: Z→ Coil G n p,Bumps T.span g∧ (∀ d,g (T.call d)=Y d)∧∀ z∈T.span, ‖g z‖≤2*w⁻¹*a:=by
    apply sprigs hv ha (inv_nonneg.mpr hp.le); intro S v c hc hM
    obtain ⟨f',hf,hQ⟩:= hM.afloat; let x:= ∑ i∈S,v i • Y i; have ht:= Eyelet.castL x
    refine ht.tsum_eq.symm.trans_le (b:=_) ?_; suffices hp': SumBudget (fun i=> ‖x i‖) (w⁻¹*c) from hp'.2.2
    refine budget_mono (budget_scale (inv_nonneg.mpr hp.le) (budget_pull (fun x:StockTag n=>x.val) Subtype.val_injective (hQ ()))) (fun i=> norm_nonneg _) (fun i=>?_)
    have hh:0 < Eyelet.fee p i.val.1:= Eyelet.toll_pos ..
    rw [show w⁻¹ * ((boxGoal G n p|>.cost () i.val)*f' i.val) = (Eyelet.fee p i.val.1 / w)*f' i.val from ?_]; swap; · change _=_*_; change w⁻¹ * (Eyelet.fee p i.val.1*_)= _; ring
    refine (BoundedContinuousFunction.norm_le (mul_nonneg (div_pos hh hp).le ((hf _).1))).2 fun U=>?_
    change ‖tire p i U x‖≤ _; let p₀:ℝ:=Eyelet.fee p i.val.1 / w; rw [show tire p i U x=(p₀:ℂ)*∑ j∈S,v j* f j i.val U.tag from ?_,norm_mul,Complex.norm_real,Real.norm_of_nonneg (div_pos hh hp|>.le)]
    · exact mul_le_mul_of_nonneg_left ((hf _).2 _) (div_pos hh hp|>.le)
    unfold x; rw [map_sum,Finset.mul_sum]; simp_rw [map_smul,hr]; exact Finset.sum_congr rfl fun j _=>mul_left_comm ..

end YM.UVExtension.Rafter

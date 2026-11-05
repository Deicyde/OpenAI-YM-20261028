import YM.AnalyticNext.QUARTIC_MATCH.Cells.Inside
import YM.AnalyticNext.QUARTIC_MATCH.Estimate.Depot
import YM.Next.FREE_KERNELS.Differences



/-!
# Tangent against every input link

Both memberships for estimates. µ pricing rather than the more costly tree
sheet argument. Spin component exactly zero here; not omitting mixed spin
variations in rough kernel.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticNext.QuarticMatch.Local
open Filter Function Lattice Laurent Matrix Hessian Analysis RG Precision Exterior Bid Wilson Branch Bloch
open Progress.StationaryScenes Work.F03 YM.Next.Free Work.F08 Pre.Centered
open Joint Estimate Estimate.Purse Estimate.Logfee Estimate.Depot BoxChain
open scoped Topology Matrix.Norms.Frobenius ContDiff BigOperators InnerProductSpace
attribute [local instance] Gauge.frobInner
variable {G : Gauge} {n l c f : Side} {ι : Type} [DecidableEq ι]
namespace Evoke
variable (S : StepData c f)
open Green (wt)

/-- One smooth or rough input. -/
def Presents (S : StepData c f) (P : Purse ι (Site f)) (k : ι) (x : Pre.Centered.JointSpace G c f) :=
    (∀ i : TypeFace 1, P.Pays {k} (fun y => x.2.1 (y,i)) (S.patch.L.val:ℝ)⁻¹) ∧
      (∀ j : PlaqAxes,P.Pays {k} (fun y => faceCurl (y,j) x.2.1) ((S.patch.L.val:ℝ)^2)⁻¹) ∧
    (∀ i : TypeFace 1,(Yard.cap S P).Pays {k} (fun y => x.1 (y,i)) 1) ∧ (Yard.cap S P).Pays {k} x.2.2 1
omit [DecidableEq ι] in
lemma lays (P : Purse ι (Site f)) (v : ι→Pre.Centered.JointSpace G c f) (h : ∀ i,Presents S P i (v i)) :
    Income S P v ∧ Plaque.BendBill S.patch.L P (fun i => (v i).2.1) := by
  refine ⟨⟨fun i k => (h i).1 k,fun i k => ?_,fun i => (h i).2.2.2⟩,fun i => (h i).2.1⟩
  simpa only [PNat.val_ofNat, Nat.cast_one,inv_one] using (h i).2.2.1 k

local notation "L" => (S.ratio.count.val:ℝ)
lemma accrual (y x : Site c) (η : ℝ) : wt (η/L) (S.ratio.embed x) (S.ratio.embed y)=wt η x y := by
  unfold wt; rw [le_antisymm (scaled_root S.ratio ..) (Corona.below S.ratio ..)]
  push_cast; field_simp
lemma cross (y : Site c) (x : Site f) (η : ℝ) : wt (η/L) x (S.ratio.embed y)=crossW S.ratio η x y := by unfold wt crossW; ring_nf

lemma point (p : Body 1 c) (u : G.Color) (j : G.ColorIndex) : parts G 1 (sparse (shape 1 p) u) j = Pi.single p (u j) := by
  funext i; unfold parts; rw [sparse_at]
  by_cases hh : i=p
  · subst i; simp
  rw [Pi.single_eq_of_ne hh, if_neg ?_]; rfl
  intro h; apply hh; apply Prod.ext (show i.1=p.1 from congr_arg (fun j : Cell (Per c) => j.1) h.symm); exact Subtype.ext (congr_arg (fun x : Cell (Per c) => x.2) h.symm)

/-- Curled output. -/
lemma faces {a : Dir G f} (p : PlaqAxes) (x : Site f) : faceCurl (x,p) a =
    a (x+step p.val.1,coord p.val.2) - a (x,coord p.val.2) - (a (x+step p.val.2,coord p.val.1)-a (x,coord p.val.1)) := by
  ext i; exact d_plaquettes x p (parts _ _ _ i)

/-- Stencil bills needed. -/
def motion (S : StepData c f) (U : Cross S.ratio.count (TypeFace 1) (TypeFace 1)) (η C : ℝ) :=
    ∀ m : List Axis,m.length ≤ 1 → (advanceC S.ratio.count U m).strip η (C/(S.ratio.count.val:ℝ)^(1+m.length))

def coverCharge (η C : ℝ) := max 1 (Real.exp η * (Fintype.card (TypeFace 1):ℝ)*max 1 C)
lemma cover_ge (η C : ℝ) : 1 ≤ coverCharge η C := le_max_left ..
lemma covering {η C D : ℝ} (he : 0 ≤ η) (hη : η ≤ D) (V : Cross S.ratio.count (TypeFace 1) (TypeFace 1))
    (n : ℕ) (h : V.strip D (C/L^n)) (i : Body 1 f) (x : Body 1 c) : wt (η/L) i.1 (S.ratio.embed x.1)*‖installed S.ratio V i x‖ ≤ coverCharge D C / L^n := by
  have hs := cross_sprawl S.ratio (he.trans hη) h i
  calc
    _ ≤ crossW S.ratio D i.1 x.1 * ‖installed S.ratio V i x‖ := by
      rw [cross]; apply mul_le_mul_of_nonneg_right _ (norm_nonneg _); apply Real.exp_monotone; gcongr
    _ ≤ _ := (Finset.single_le_sum (f:=fun x : Body 1 c => crossW S.ratio D i.1 x.1 * ‖installed S.ratio V i x‖)
      (fun _ _ => mul_nonneg (Real.exp_pos _).le (norm_nonneg _)) (Finset.mem_univ _)).trans hs
    _ ≤ _ := by
      rw [← mul_div_assoc,← mul_div_assoc]; apply div_le_div_of_nonneg_right _ (by positivity)
      apply le_trans _ (le_max_right 1 _); rw [← mul_assoc]; gcongr; exact le_max_right ..

def smoothC (η C : ℝ) := 2*coverCharge η C
lemma costS (η C : ℝ) : 1 ≤ smoothC η C := (cover_ge ..).trans (le_mul_of_one_le_left (zero_le_one.trans (cover_ge ..)) one_le_two)
def external (U : Matrix (Body 1 f) (Body 1 c) ℝ) (x : Cell (Per c)) (u : G.Color) : Pre.Centered.JointSpace G c f :=
    (sparse x u, stance U (sparse x u))

omit [DecidableEq ι] in
lemma offers {η D C} (hp : 0<η) (hη : η ≤ D) (V : Cross S.ratio.count (TypeFace 1) (TypeFace 1)) (H : motion S V D C)
    (P : Purse ι (Site f)) (y : Cell (Per c)) (u : G.Color) (k : ι) (hk : P.mark ≠ some k) (hx : P.amps k = smoothC D C * ‖u‖)
    (hP : ∀ z, P.toll k z=wt (η/L) z (S.ratio.embed y.1)) : Presents S P k (external (installed S.ratio V) y u) := by
  have he : ¬ P.tagged {k} := by simp [Purse.tagged,hk]
  let U := installed S.ratio V; let q := external U y u
  by_cases h : y.2.card=1
  · let b : Body 1 c := (y.1,⟨y.2,h⟩)
    have hw : shape 1 b=y := rfl
    have ht i (z : Body 1 f) : parts G 1 q.2.1 i z=U z b*u i := by
      change (U *ᵥ parts G 1 (sparse y u) i) z=_
      rw [show parts G 1 (sparse y u) i=Pi.single b (u i) from hw ▸ point b u i, Matrix.mulVec_single]; simp [mul_comm]
    have hm : V.strip D (C/L^1) := by simpa only [List.length_nil,advanceC,add_zero,← one_div] using H [] (by simp)
    let v := coverCharge D C; let w := smoothC D C
    have hD (i : Axis) : (advanceC S.ratio.count V [i]).strip D (C/L^2) := H [i] (by simp)
    have hp' := hp.trans_le hη
    have hf (i : Axis) : installed S.ratio (advanceC _ V [i])=(knock _ i).acts f * U := by
      have h := flow_movement S.ratio V [i] S.patch.odd_side (fun t ht => ⟨D,_,hp',H t ht⟩)
      rw [motion_walk,motion_zero, Matrix.mul_one] at h; exact h
    have hy (i : Axis) (p : TypeFace 1) (z : Site f) : let t' := q.2.1 (z+step i,p) - q.2.1 (z,p)
        wt (η/L) z (S.ratio.embed y.1)*‖t'‖ ≤ v/L^2*‖u‖ := by
      intro t'
      let A := advanceC S.ratio.count V [i]
      have hh : t'=installed S.ratio A (z,p) b • u := by
        ext j
        change parts G 1 q.2.1 j _-parts G 1 q.2.1 j _ = installed S.ratio A (z,p) b*u j
        rw [ht,ht, hf i]
        change _=((knock (TypeFace 1) i).acts f *ᵥ (fun x => U x b)) (z,p)*_
        rw [knock_entry]; dsimp only; ring
      rw [hh,norm_smul,← mul_assoc]; exact mul_le_mul_of_nonneg_right (covering S hp.le hη A 2 (hD i) (z,p) b) (norm_nonneg _)
    have hL := side_pos S.ratio.count
    change Presents _ _ _ q
    refine ⟨fun i => ⟨by positivity,fun _ z => ?_,fun hh => (he hh).elim⟩,fun i => ⟨by positivity,fun _ z => ?_,fun hh => (he hh).elim⟩,
      fun i => ⟨zero_le_one,fun _ z => ?_,fun hh => (he hh).elim⟩,Pays.zero zero_le_one⟩
    · have hh : q.2.1 (z,i)=U (z,i) b • u := by ext j; exact ht j _
      simp only [price,target, Finset.prod_singleton, Finset.prod_singleton,hP,hx,hh,norm_smul,← mul_assoc]
      have hX := covering S hp.le hη V 1 hm (z,i) b; rw [pow_one] at hX
      apply ((mul_le_mul_of_nonneg_right hX (norm_nonneg u))).trans
      change v/L*_ ≤ L⁻¹*w*‖u‖
      apply mul_le_mul_of_nonneg_right _ (norm_nonneg _)
      rw [inv_mul_eq_div]; refine div_le_div_of_nonneg_right ?_ hL.le; exact le_mul_of_one_le_left (zero_le_one.trans (cover_ge ..)) one_le_two
    · simp only [price,target, Finset.prod_singleton, Finset.prod_singleton,hP,hx, faces]
      apply ((mul_le_mul_of_nonneg_left (norm_sub_le ..) (Green.wt_pos ..).le)).trans
      rw [mul_add]; exact (add_le_add (hy _ _ z) (hy _ _ z)).trans_eq
        (show v/L^2*‖u‖ + v/L^2*‖u‖=(L^2)⁻¹*(2*v*‖u‖) from by ring)
    · rw [Yard.cap_price, show (Yard.cap S P).target {k}=P.target _ from rfl,price,target,
        Finset.prod_singleton, Finset.prod_singleton,hP,hx,one_mul]
      change _* ‖sparse y u (z,i)‖ ≤ _
      rw [sparse_at]; split
      · next h => rw [show y.1=z from congr_arg Prod.fst h, Green.wt,separation_self,
          Nat.cast_zero,mul_zero,Real.exp_zero,one_mul]; exact le_mul_of_one_le_left (norm_nonneg _) (costS ..)
      rw [norm_zero,mul_zero]; exact mul_nonneg (zero_le_one.trans (costS ..)) (norm_nonneg _)
  · rw [external,sparse_none y u h, map_zero];
    refine ⟨fun _ => Pays.zero (by positivity),fun i => ?_,fun _ => Pays.zero zero_le_one,Pays.zero zero_le_one⟩
    convert! Pays.zero (P:=P) (X:=G.Color) (S:={k}) (by positivity : 0 ≤ (L^2)⁻¹) using 1
    ext z j; change (d 1 f *ᵥ (0:form 1 f)) _=0; simp
end Evoke
end YM.AnalyticNext.QuarticMatch.Local

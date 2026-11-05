import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.ChipHeal
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Metering


/-!
# Read and curl in the SAME active register

The full turbine answers agree on all guarded support of plane even
when their price is not purchased on all links. Cond kernel here is
`Pcond` with retained H, identified with ``d_1 Z`` when on *those*
representatives and σ, not recovering rotations of a different Hessian.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Remote
open Filter Function Lattice RG RG.Patch Wilson Finset Pressure Pressure.Tube Precision Exterior Bloch Matrix
open Next.Fluctuations Next.SectorChange Motion Rows Push.SectorMeasure  Pressure.Stores Gaussian Tree Wisps Bid
open Assembly Current FreeResolvent
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius BigOperators Classical ContDiff
variable {G : Gauge} {c f n : Side} {S : StepData c f} {x : ℝ}

abbrev tileP := FreeResolvent.Slot G f 2
lemma onTurn (S : StepData c f) (F : Forest S.ratio) (i : tileP (G:=G) (f:=f)) (j : FreeResolvent.Active G F) (h : plane S F i j ≠ 0) :
    separation (seat S 2 i) (theta S.ratio F j) ≤ 1 := by
  rw [plane_sub] at h
  let k:=j.1.val; let b:Body 1 f := (k.1,coord k.2)
  obtain ⟨y,a,l⟩ := i
  obtain ⟨p,rfl⟩ := plaqEquiv.surjective a
  change separation (S.ratio.parent y) (S.ratio.parent k.1) ≤ _
  by_contra! hh
  have hx (x : Site f) (z : TypeFace 1) (hx : separation (S.ratio.parent y) (S.ratio.parent x) ≤ 1) :
      (Pi.single (M:=fun _ => ℝ) b 1 (x,z)) = 0 := by rw [Pi.single_apply,if_neg]; intro h; have he := congr_arg Prod.fst h; change x=k.1 at he; rw [he] at hx; omega
  have hg := d_plaquettes y p (Pi.single b 1)
  rw [hx (y+step p.val.1) _ (Work.E03.parent_step S ..),hx y _ (by simp),hx (y+step p.val.2) _ (Work.E03.parent_step S ..),hx y _ (by simp)] at hg
  simp only [sub_zero] at hg
  have hz : d 1 f (y,plaqEquiv p) b=0 := by
    let t := d 1 f *ᵥ Pi.single b 1
    have hb : t (y,plaquette p)=0 := hg
    simpa [t,mulVec,dotProduct,Pi.single_apply,mul_ite] using hb
  apply h
  unfold tensor plant ix
  simp only [Matrix.submatrix_apply,id_eq,Matrix.of_apply]; split
  exact hz
  rfl

variable (U : Stores S) (F : Forest S.ratio)

def loadLink (x : ℝ) : In x U F (G:=G) ↪ FreeResolvent.Active G F where
  toFun i:=(i.1.val,i.2)
  inj' _ _ h:=Prod.ext (Subtype.ext (congr_arg Prod.fst h)) (congr_arg (fun i : FreeResolvent.Active G F=>i.2) h)
lemma stationId {o : Site c} {D : ℕ} (he : Clears U x o D) (j : FreeResolvent.Active G F) (hh : separation o (theta S.ratio F j)≤D) :
    j ∈ Set.range (loadLink (G:=G) U F x) := ⟨(⟨j.1,live_test U F he _ hh⟩,j.2),rfl⟩

def dKeys (x : ℝ) := (plane S F (G:=G)).submatrix id (loadLink U F x)

def rainbow (x : ℝ) (Y : Gaussian.Table (In x U F (G:=G))) := dKeys U F x * mirror Y * (dKeys U F x).transpose

lemma sandwich {ι B ν : Type} [Fintype ι] [Fintype B] (Y : Gaussian.Table ι) (Z : Gaussian.Table B)
    (d : ι→B) (he : Injective d) (P : Matrix ν B ℝ) (i j : ν)
    (hh : ∀ k, P i k ≠ 0 ∨ P j k ≠ 0 → k∈Set.range d) (M E : ℝ) (hM : 0≤M)
    (hp : ∑ k, |P i k| ≤ E) (hs : ∑ k, |P j k| ≤ E)
    (hm : ∀ k w, P i (d k) ≠ 0 → P j (d w) ≠ 0 → |Y k w-Z (d k) (d w)| ≤ M) :
    let R := P.submatrix id d
    |(R*Y*R.transpose) i j-(P*Z*P.transpose) i j| ≤ E^2*M := by
  have hE : 0≤E := (Finset.sum_nonneg (fun k _ => abs_nonneg _) (s:=univ) (f:=fun k => |P j k|)).trans hs
  intro R; simp only [mul_apply,transpose_apply,Finset.sum_mul]
  let Q (x y : B) := P i y*Z y x*P j x
  have inject (u : B→ℝ) (ht : ∀ i∉Set.range d, u i=0) : ∑ x, u x=∑ x,u (d x) := by
    classical
    rw [← Finset.sum_image (f:=u) (g:=d) he.injOn]; symm
    refine Finset.sum_subset (Finset.subset_univ _) (fun i _ hh => ht i (fun ⟨a,e⟩ => hh (Finset.mem_image.mpr ⟨a,Finset.mem_univ _,e⟩)))
  rw [show ∑ x : B, ∑ y, Q x y = ∑ x : ι, ∑ y, Q (d x) (d y) from ?_]
  swap
  · rw [inject (fun x => ∑ y,Q x y)]; refine Finset.sum_congr rfl fun x _ => inject _ (fun z hz => ?_)
    · unfold Q; rw [show P i z = 0 from by by_contra h; exact hz (hh z (Or.inl h))]; ring
    intro z hz; unfold Q; simp only [show P j z=0 from (by by_contra h; exact hz (hh z (Or.inr h))),mul_zero,Finset.sum_const_zero]
  simp_rw [← sum_sub_distrib]; unfold R Q; simp only [Matrix.submatrix_apply,id_eq]
  refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum fun z _ => (abs_sum_le_sum_abs ..).trans (sum_le_sum (g:=fun y => |P i (d y)| * M * |P j (d z)|) fun y _ => ?_)).trans ?_)
  · by_cases hi : P i (d y)=0
    · simp [hi]
    by_cases hu : P j (d z)=0
    · simp [hu]
    rw [show P i (d y)*Y y z*P j (d z)- P i (d y)*Z (d y) (d z)*P j (d z)=P i (d y)*(Y y z-Z (d y) (d z))*P j (d z) by ring,abs_mul,abs_mul]; gcongr; exact hm _ _ hi hu
  simp_rw [← sum_mul,← Finset.mul_sum]
  have H (p : ν) : ∑ k : ι, |P p (d k)|≤∑ k, |P p k| := Cost.sum_comp_le he _ (fun k => abs_nonneg _) -- check
  calc
    _ ≤ (E*M)*E := by gcongr; exacts [(H i).trans hp,(H j).trans hs]
    _ = _ := by ring

lemma half_keep {a b x : ℝ} (h : |a| ≤ x) (ht : |b|≤x) : |(1/2:ℝ)*(a+b)|≤ x := by
  rw [abs_mul,abs_of_pos (by norm_num : 0<(1/2:ℝ))]
  have he := abs_add_le a b; linarith
lemma curlize (x : ℝ) (z : Site c) (D d : ℕ) (h : Clears U x z D) (he : d+1≤D)
    (Y : Gaussian.Table (In x U F (G:=G))) (X : Gaussian.Table (In x (bareStores S) F (G:=G))) (M : ℝ) (hM : 0≤M)
    (hi : ∀ a b, separation z (front U F b)≤d+1 → |Y a b-X (official U F a) (official U F b)|≤M) (a b : tileP (G:=G) (f:=f))
    (ha : separation z (seat S 2 a)≤d) (hb : separation z (seat S 2 b)≤d) :
    let L:=opened G S x (bareStores S) F (bare_is_Clear S x F)
    |rainbow U F x Y a b-(plane S F (G:=G)*mirror (X.submatrix L L)*(plane S F (G:=G)).transpose) a b|≤
      (curlTariff G S.patch 0)^2*M := by
  intro L
  have hx (i : tileP (G:=G) (f:=f)) : ∑ k, |plane S F i k| ≤ curlTariff G S.patch 0 := by
    simpa only [Cost.weight_zero,one_mul] using (plane_price S F 0 le_rfl).rows.bound i
  have hw (q : tileP (G:=G) (f:=f)) (hq : separation z (seat S 2 q)≤d) (i : FreeResolvent.Active G F) (h : plane S F q i≠0) :
      separation z (theta S.ratio F i) ≤ d+1 := (separation_triangle z (seat S 2 q) _).trans (Nat.add_le_add hq (onTurn S F q i h))
  let u:=loadLink (G:=G) U F x
  refine sandwich (mirror Y) (mirror (X.submatrix L L)) (loadLink U F x) u.injective (plane S F) a b (fun i h => ?_) M (curlTariff G S.patch 0) hM (hx _) (hx _) fun i j hx hz => ?_
  · rcases h with hi|hi -- shadow
    · exact stationId U F ‹Clears U x z D› i ((hw a ha _ hi).trans he)
    exact stationId U F ‹Clears U x z D› i ((hw b hb _ hi).trans he)
  have h1 := hi i j (hw b hb (loadLink U F x j) hz)
  have h2 := hi j i (hw a ha (loadLink U F x i) hx)
  change |(1/2:ℝ)*(Y i j+Y j i) - 1/2*(X (L (u i)) (L (u j))+X (L (u j)) (L (u i)))|≤M
  have hu (i : In x U F (G:=G)) : L (u i)=official U F i := rfl
  simp_rw [hu]; generalize X (official U F i) (official U F j)=A, X (official U F j) (official U F i)=B at *
  -- alternative don't generalize
  rw [show (1 / 2:ℝ) * (Y i j + Y j i) - 1 / 2 * (A+B)=1/2*((Y i j-A)+(Y j i-B)) by ring]; exact half_keep h1 h2
end YM.AnalyticBridge.LocalGaussianLaws.Remote

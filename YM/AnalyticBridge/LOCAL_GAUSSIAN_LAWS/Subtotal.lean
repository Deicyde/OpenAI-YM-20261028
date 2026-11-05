import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.DensityPrice
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Staged
import YM.AnalyticBridge.LOCAL_GAUSSIAN_LAWS.Watch

/-!
# Subtotal before inversion

The stock is prepared on two prices: one for V in a common axial
gauge's actual chord size on every stencil being used, another for
the extension for linear $b_1$ about same area. They share t after
`Lift.Enclave`. Tilde and support conventions throughout. With the mean
from that same sector, D-transpose invoiced AT input columns, active-frame
link configurations unchanged. All orientations evaluated. $A\nu+b$
sup deliberately overcount `cuts` and polynomial multiplicity. Even for
the omitted part, `widen` may overcount. No bound at a clamped Coarse
link outside these local choices. But can apply to all columns tested in
the local inversion. Both Pane geometries addressed next.
-/
set_option autoImplicit false
noncomputable section
namespace YM.AnalyticBridge.LocalGaussianLaws.Lift
open Function Filter Lattice RG Wilson Finset Pressure Pressure.Stores Pressure.Tube Precision Exterior Tree Bloch Bid Matrix
open Next Next.Fluctuations SectorChange SectorChange.Rows SectorChange.Gaussian Push.SectorMeasure  Remote Wisps Oriented
open scoped Topology InnerProductSpace BigOperators ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {c f n : Side} {S : StepData c f} {x t : ℝ}

def Booth (Pt : Teller G) (S : StepData c f) (T : Tube G S) := Pt.Funds S T ∧ ∃ (H L : Bed) (a b v w : ℝ),
  Floor H T.high f a b ∧ Floor L T.low c v w ∧ Attached H T.up ∧ Attached L T.down ∧ Sworn H f G ∧ Sworn L c G ∧
  Towers.Diagonal S H L T.R ∧ Towers.Roll S H L T.R T.high T.low

def credit (U : Stores S) (F : Forest S.ratio) (V : Config G c) (T : Tube G S) (k : S.Choices) (q : Chi) (d : ℝ)
    (Y : LinkArray G (Frozen U x F)) (Z : Dir G c) := direct T x V k (shots S x) U F q d Y (marked U x F (doc T F Z))

lemma accounting (G : Gauge) (P : Patch) (K : KernelChoices) (Pt : Teller G) (h : P.Branches Pt.bind G) (he : Pt.bind=K) :
    ∃ A δ τ : ℝ, 0≤A ∧ 0<δ ∧ 0<τ ∧ ∀ᶠ x : ℝ in atTop,
    ∀ t, 0≤t → t≤δ → ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Booth Pt S T →
    ∀ (U : Stores S) (o : Site c) (F : Forest S.ratio), Clears U x o (radiusB x) → ∀ V : Config G c, U.flags=RG.flags (temp x) V →
    ∀ v : Dir G c, ‖v‖ ≤ t → paid S (replica S.ratio V) o (radiusB x) t → AgreeNear id o (radiusB x) V (represent v) →
    ∀ (k : S.Choices) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen U x F)) (i : Receipt G S), separation o (Wisps.down S i) ≤ radiusB x/2 →
      |credit U F V T k q d Y v i| ≤ A*t*widen (till x) t τ := by
  obtain ⟨A,δ,τ,ha,hd,hτ,H⟩ := base_summary Pt P h
  obtain ⟨X,hX,hW⟩ := carry_summary G P K Pt
  let s:=Pt.top.width; let C:=Pt.top.paths; let p:=Pt.top.clip; have hs : 0<s := Pt.top.width_pos
  obtain ⟨Z,γ,hZ,hγ,h⟩ := prepared G P K p C s (he ▸ h) Pt.top.paths_pos.le hs
  refine ⟨slip*(A+Z*X),min δ γ,min s τ,mul_nonneg slip_pos.le (add_nonneg ha (mul_nonneg hZ hX)),lt_min hd hγ, lt_min hs hτ,?_⟩
  filter_upwards [H,small_span P] with x hx hQ
  intro t ht hu c f S T hP hp U o F H0 V hA v hv hV hV' k q d Y i hi
  obtain ⟨hT,L,J,c₀,D,a,b,H4,H5,hL,hJ,hw,hw',hD,hR⟩ := hp
  have hk : S.kernel=K := hT.knobs.trans he
  have hh : T.high=p := hT.high
  obtain ⟨K',P',h1,h2⟩ := hT.feeds
  rw [← hT.high] at h1; rw [← hT.low] at h2
  have H3 : S.patch.Branches S.kernel G := by rw [hT.knobs]; exact hT.kernel
  let m := doc T F v
  have H6 : separation o (Remote.aim S i.1)+span P x≤radiusB x := by change separation o (Remote.aim S i.1) ≤ _ at hi; omega
  obtain ⟨HB,HC⟩ := h t ht (hu.trans (min_le_right ..)) S hP hk T K' hh (hh ▸ h1) U F x o _ V hV H0 k i.1 H6
  have hl := HB m (doc_trunk T F v)
  have hy := hx S T hP hT U o H0 V v t hA hV' hv (hu.trans (min_le_left ..)) k i.1.1 i.1.2 hi
  have HZ := congr_fun (rowzero T F k v L J H3 hL h1 H4 hw hJ h2 H5 hw' hD hR) i.1
  change Flat.ideal T m i.1 + firstTerm T v i.1=0 at HZ
  unfold credit Rows.direct; rw [moved T x V k (shots S x) U F h1,Rows.source, selected]
  let z:= base T x V k+(bump T x V k (fresh x (shots S x) U F (tape (marked U x F m))))
  by_cases hu' : keep x (shots S x) U F i.1
  · simp only [Pi.add_apply] -- unfolds? expose coordinate
    set w := autoShell q d V Y
    let u:=input x U F w
    have hi : tape.symm (Rows.restrict x (shots S x) U F (bump T x V k (fresh x (shots S x) U F (tape (marked U x F (doc T F v)))))) i+
        tape.symm (Rows.restrict x (shots S x) U F (Rows.base T x V k+bump T x V k u)) i=(slip • z i.1) i.2 := by
      change (Rows.restrict x (shots S x) U F _ i.1) i.2+(Rows.restrict x (shots S x) U F _ i.1) i.2=_
      unfold Rows.restrict; simp only [if_pos hu',Pi.add_apply]; rw [show bump T x V k u i.1=0 from HC w,add_zero,show z i.1=Rows.base T x V k i.1+bump T x V k (fresh x (shots S x) U F (tape (marked U x F (doc T F v)))) i.1 from rfl,smul_add,add_comm (slip • Rows.base T x V k i.1)]; rfl
    rw [hi]
    let e := widen (till x) t (min s τ); have hB : 0≤e := widen_nonneg _ ht
    refine (PiLp.norm_apply_le (slip • z i.1) _).trans ?_
    rw [norm_smul, Real.norm_of_nonneg slip_pos.le, mul_assoc slip, mul_assoc slip]
    apply mul_le_mul_of_nonneg_left _ slip_pos.le
    have ht0 : ‖z i.1‖ ≤ ‖Rows.base T x V k i.1-firstTerm T v i.1‖+‖bump T x V k (fresh x (shots S x) U F (tape (marked U x F m))) i.1-Flat.ideal T m i.1‖ := by
      rw [show z i.1=(Rows.base T x V k i.1-firstTerm T v i.1)+(bump T x V k (fresh x (shots S x) U F (tape (marked U x F m))) i.1-Flat.ideal T m i.1) from ?_]; exact norm_add_le ..
      calc
        _ = z i.1 - (Flat.ideal T m i.1+firstTerm T v i.1) := by rw [HZ,sub_zero]
        _ = _ := by unfold z; rw [Pi.add_apply]; abel
    refine ht0.trans ((add_le_add hy hl).trans ?_)
    have h1' : widen (till x) t τ ≤ e := widen_anti _ _ (min_le_right ..)
    have h2' : widen (till x) t s ≤ e := widen_anti _ _ (min_le_left ..)
    have hX' : ‖m‖ ≤ X*t := (hW S T hP hk hT F v).trans (mul_le_mul_of_nonneg_left hv hX) -- needs H? carry requires only hP h0 hT check
    calc
      _ ≤ A*t*e+Z*(X*t)*e := add_le_add (mul_le_mul_of_nonneg_left h1' (by positivity)) (mul_le_mul (mul_le_mul_of_nonneg_left hX' hZ) h2' (widen_nonneg _ ht) (by positivity))
      _ = _ := by unfold e; ring
  have hN (Q : LogArray G (Slots S)) : tape.symm (Rows.restrict x (shots S x) U F Q) i=0 := by change (Rows.restrict x _ _ _ _ i.1) i.2=_; rw [Rows.restrict,if_neg hu']; rfl
  rw [Pi.add_apply,hN,hN,add_zero,abs_zero]; have ht' := (widen_nonneg (τ:=min s τ) (till x) ht); have hs := slip_pos; positivity
lemma individual (U : Stores S) (F : Forest S.ratio) (V : Config G c) (k:S.Choices) (T : Tube G S) (x : ℝ) {C : ℝ} {s : ℝ} (hs : 0≤s) (hC : 1≤C)
    (h : (FreeResolvent.native c).Schur (front U F) (front U F) s C (Rows.gram T x V k (shots S x) U F))
    (i : Receipt G S) (j : In x U F (G:=G)) : |Rows.move T x V k (shots S x) U F i j| ≤ C := by
  let M := Rows.move T x V k (shots S x) U F
  have hh := (h.rows.mono hs le_rfl).weighted j j
  rw [FreeResolvent.Cost.weight_zero, one_mul, Rows.gram,mul_apply] at hh
  have ht : (M i j)^2 ≤ C := by
    apply le_trans _ (le_of_abs_le hh); rw [sq]
    exact Finset.single_le_sum (fun i _ => mul_self_nonneg (M i j)) (mem_univ i)
  change |M i j| ≤ C
  have hQ : |M i j|^2 ≤ C := (sq_abs ..).trans_le ht
  nlinarith

-- Spent means at locally reached columns. `η s K N e b` constant
-- numbers of SAME quote; no surrender the coupling normalization.
lemma spacing {V : Type} [Fintype V] [DecidableEq V] {c : Side} (Q : Gaussian.Table V) (W : V → Set V) (Ω : V → Site c) {ρ η K N e b : ℝ}
    (h : Closes (FreeResolvent.native c) Ω Q W ρ K η N e b) (hρ : 0 ≤ ρ) (_hK : 0≤K) (_hN : 0≤N) (x y : V→ℝ) {C D : ℝ} (hC : 0≤C) (hD : 0≤ D) (hc : ∀ i, |x i| ≤ C) (i : V)
    (hd : ∀ j∈W i, |(Q*ᵥ x+y) j| ≤ D) :
    |offCenter (pane W Q 0) y i - x i| ≤ N*D+K*e*C := by
  obtain ⟨hp,-,hh,-⟩ := h.issuer 0 le_rfl
  simp only [zero_smul,add_zero,inv_one,mul_one] at hh hp
  let A:=pane W Q 0; let P:=Q*A-1
  have ht : offCenter (pane W Q 0) y-x=P.transpose*ᵥx-A.transpose*ᵥ (Q *ᵥ x+y) := by
    rw [show P=Q*A-1 from rfl,Matrix.transpose_sub,Matrix.transpose_mul, show Q.transpose=Q from (Matrix.isHermitian_iff_isSymm.mp h.primal.isHermitian).eq,Matrix.transpose_one,Matrix.sub_mulVec,← Matrix.mulVec_mulVec,Matrix.one_mulVec,Matrix.mulVec_add,offCenter,Matrix.neg_mulVec]; abel
  change |(offCenter (pane W Q 0) y-x) i|≤_
  rw [ht,Pi.sub_apply,add_comm (N*D)]; apply (abs_sub _ _).trans; gcongr
  · unfold mulVec dotProduct; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun i1 => |P i1 i| *C) (fun i1 _ => by rw [abs_mul]; exact mul_le_mul_of_nonneg_left (hc i1) (abs_nonneg (P i1 i)))).trans ?_)
    rw [← sum_mul]; apply mul_le_mul_of_nonneg_right _ hC; simpa only [FreeResolvent.Cost.weight_zero,one_mul,transpose_apply] using (hh.cols.mono hρ le_rfl).bound i
  unfold mulVec dotProduct; refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun i1 => |A i1 i| *D) (fun i1 _ => ?_)).trans ?_)
  · rw [abs_mul]; change |A i1 i| *_ ≤ _; by_cases hx : i1∈ W i; gcongr; exact hd i1 hx
    rw [show A i1 i=0 from pane_absent W Q 0 (Or.inr hx)]; simp
  rw [← sum_mul]; apply mul_le_mul_of_nonneg_right _ hD; simpa only [FreeResolvent.Cost.weight_zero,one_mul,Matrix.transpose_apply] using (hp.cols.mono hρ le_rfl).bound i

open FreeResolvent in
theorem focused (G : Gauge) (P : Patch) (K : KernelChoices) (Pt : Teller G) (h : P.Branches Pt.bind G) (he : Pt.bind=K) :
    ∃ A X s E N M τ δ : ℝ, 0≤A ∧ 0≤X ∧ 0<s ∧ 0≤E ∧ 1≤N ∧ 1≤M ∧ 0<τ ∧ 0<δ ∧ ∀ᶠ x in atTop,
    ∀ t, 0≤t → t≤δ → ∀ {c f : Side} (S : StepData c f) (T : Tube G S), S.patch=P → Booth Pt S T → 100*(1+radiusB x)≤c.val →
    ∀ (U : Stores S) (o : Site c) (F : Forest S.ratio), Clears U x o (radiusB x) → ∀ V : Config G c, U.flags=RG.flags (temp x) V →
    ∀ v : Dir G c, ‖v‖ ≤ t → paid S (replica S.ratio V) o (radiusB x) t → AgreeNear id o (radiusB x) V (represent v) →
    ∀ (k : S.Choices) (q : Chi) (d : ℝ) (Y : LinkArray G (Frozen U x F)),
    let a:=marked U x F (doc T F v); let D:= pieces P G*LocalJet.grain (span P x); let R := radiusB x
    ∀ i : In x U F (G:=G), separation o (front U F i) ≤ R/4 → ∀ g : Assembly.Geometry,
      let Q:=Rows.gram T x V k (shots S x) U F; let b:=blame T x V k (shots S x) U F q d Y
      let ν:=pane (Assembly.sectorW G S x U F g) Q 0
      |offCenter ν b i-a i| ≤ N*(D*M*(A*t*widen (till x) t τ))+M*(E*Real.exp (-s*R))*(X*t) := by
  obtain ⟨A,δ,τ,hA,hδ,hτ,H⟩ := accounting G P K Pt h he
  obtain ⟨η,s,M,N,E,gap₀,-,hs,hM,hN,hE,-,HH⟩ := LocalGaussianLaws.quote G P Pt h
  obtain ⟨X,hX,h'⟩ := carry_summary G P K Pt
  refine ⟨A,X,s,E,N,M,τ,δ,hA,hX,hs,hE.le,hN,hM,hτ,hδ,?_⟩
  filter_upwards [H,HH,Work.E01.radiusB_tendsto.eventually_ge_atTop 200,small_span P] with x H hh hv hq
  intro t ht hT c f S T hp hb hc U o F h0 V hV v hw hV' hy k q d Y a D R i hi g Q b ν
  obtain ⟨h₁,h₂⟩ := hh.2 S T hp hc hb.1 U F k V hV
  have hS : S.patch.Branches S.kernel G := by rw [hb.1.knobs]; exact hb.1.kernel
  let Z:=Assembly.sectorW G S x U F g; let e:=E*Real.exp (-s*R)
  have hz : Closes (native c) (front U F) Q Z s M η N e gap₀ := by cases g; exact h₁; exact h₂
  have hW := widen_nonneg (till x) (τ:=τ) ht; have hm : 0≤M := by linarith
  have hD : 0≤D := mul_nonneg (pieces_nonneg P G) (Nat.cast_nonneg _)
  refine spacing Q Z (front U F) hz hs.le hm (zero_le_one.trans hN) _ _ (by positivity) (by positivity) (fun j => ?_) i (fun j hj => ?_)
  · change |doc T F v j.1.val.val j.2|≤X*t
    refine (PiLp.norm_apply_le (doc T F v _) j.2).trans ?_
    exact ((norm_le_pi_norm (doc T F v) _).trans (h' S T hp (hb.1.knobs.trans he) hb.1 F v)).trans (mul_le_mul_of_nonneg_left hw hX)
  let L := Rows.move T x V k (shots S x) U F; let f' := Rows.source T x V k (shots S x) U F q d Y
  rw [show Q*ᵥ a+b=L.transpose*ᵥ (L*ᵥ a+f') from (by unfold Q b L blame Rows.gram; rw [Matrix.mulVec_add,Matrix.mulVec_mulVec])]; unfold mulVec dotProduct
  let W (y : Receipt G S) : ℝ := if separation (front U F j) (Wisps.down S y) ≤ span S.patch x then 1 else 0
  let J:=A*t*widen (till x) t τ
  refine (abs_sum_le_sum_abs ..).trans ((sum_le_sum (g:=fun y => W y*(M*J)) (fun i1 _ => ?_)).trans ?_)
  · unfold W; split
    next hl =>
      rw [abs_mul,one_mul]
      have hq' : separation o (Wisps.down S i1)≤radiusB x/2 := by
        have H:=stockBound F g hj
        have hh:=separation_triangle o (front U F i) (front U F j); have hh':=separation_triangle o (front U F j) (Wisps.down S i1)
        unfold R at hi; unfold boxCharge at H; rw [hp] at hl; omega
      exact mul_le_mul (individual U F V k T x hs.le hM hz.pays i1 j) (H t ht hT S T hp hb U o F h0 V hV v hw hV' hy k q d Y i1 hq') (abs_nonneg _) hm
    next hl => change |L i1 j*_|≤_; rw [show L i1 j=0 from move_empty U F T V k hS i1 j (lt_of_not_ge hl)]; simp
  rw [← sum_mul,mul_assoc D]; exact mul_le_mul_of_nonneg_right (by unfold D; rw [← hp]; exact down_count ..) (by unfold J; positivity)
end YM.AnalyticBridge.LocalGaussianLaws.Lift

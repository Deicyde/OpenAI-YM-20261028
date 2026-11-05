import YM.FullVolume.Mark.Nursery
/-! Countable ladder of rentals at fixed period. Total reserve outside admission lets heights and MP call spenders freely after `N→∞`.
 Cauchy and inverse-normalization. `out` x reference inverse not a bound on readout product through all future N; reconstruct only FINITE fixed-level outward maps by peeling steps. -/
set_option autoImplicit false
noncomputable section
namespace YM.MergeProof.Matric
open Function Filter MeasureTheory Finset Lattice Wilson RG Source Labels Extra.Histories Bid
open Planned.GuardedAtom Push Local Guard Motion PhysicalNext.Repeat Lotus Next.Foundations
open scoped Topology Matrix.Norms.Frobenius BigOperators ContDiff Classical
variable {G:Gauge}{d:ℕ}{F:Labels.Frame G d}{Y:Hol G}{f:ℕ→Side}{D: ∀ i,Desk G (f i)}{p c:ℕ→ℝ} {k:ℕ}
open Gram
local notation "L" => fun i=> Gram F Y (D i) (p i)
local notation "X₀"=> fun (i:ℕ)=> Club F Y (D (i+1)) (D i) (p i) (p (i+1)) (c i)
structure Gear (T:∀ i:ℕ,k ≤ i →ℕ→ Club F Y (D (i+1)) (D i) (p i) (p (i+1)) (c i)) (W:∀ m,ℕ→Gram F Y (D m) (p m)):Prop where
   tight i h:Ritzy (T i h)
   income (i:ℕ) (h:k ≤ i ):∀ᶠ n in atTop,W i n=(T i h n).flow (W (i+1) n)
variable {T:∀ i:ℕ,k ≤ i →ℕ→ Club F Y (D (i+1)) (D i) (p i) (p (i+1)) (c i)} {W:∀ m,ℕ→Gram F Y (D m) (p m)}
variable (Q: Gear T W)
namespace Gear
include Q
-- truncate as Prop; error size ≤ 2·power eventually pair. can index turns via k<n. independent k.L.
private lemma shawls (i:ℕ)(hi:k ≤ i)(d':ℕ) : ∃ V:ℕ→Gram F Y (D i) (p i),TwoFold V ∧ ∀ᶠ n in atTop, Within (W i n) (V n) (2 * (1/2:ℝ)^d'):=by
    induction d' generalizing i with
    | zero=>
       let z:= W i 0; have hp:1≤p i:=(Q.tight i hi).starts
       refine ⟨fun _=>z,fun e he=>⟨0,fun _ _ _ _=> ⟨he.le,fun v=>?_⟩⟩, Eventually.of_forall fun n=>?_⟩
       · simp only [sub_self,norm_zero];exact mul_nonneg (mul_nonneg he.le (by linarith)) (Work.G08.size_nonneg ..)
       rw [pow_zero,mul_one]; exact two _ _ (zero_le_one.trans hp)
    | succ d' ih=>
       obtain ⟨V,hV,hK⟩:= ih (i+1) (by omega); let P:=T i hi
       refine ⟨fun n=> (P n).flow (V n),(Q.tight i hi).stories hV,?_⟩
       filter_upwards [hK,Q.income i hi] with n hn h; rw [h,show 2*(1/2:ℝ)^(d'+1)=2*(1/2:ℝ)^d'/2 from by rw [pow_succ]; ring]; exact (P n).trail _ _ _ hn
lemma voyages (i:ℕ)(hi:k ≤ i ):TwoFold (W i):=by
    intro e he; let d:=e/4; have hd:0<d:=by unfold d; positivity
    obtain ⟨k,hk⟩:= ((tendsto_pow_atTop_nhds_zero_of_lt_one (r:= (1/2:ℝ)) (by norm_num) (by norm_num)).eventually (ge_mem_nhds (half_pos hd))).exists; have hq: 2*((1/2:ℝ)^k)≤ d:=by
       change (1/2:ℝ)^k ≤ d/2 at hk; linarith
    obtain ⟨V,hV,hT⟩:= shawls Q i hi k; obtain ⟨K,hK⟩:= eventually_atTop.mp hT; obtain ⟨u,hu⟩:= hV d hd
    refine ⟨max K u,fun n hn m hm=>?_⟩; obtain ⟨ha,hb⟩:= max_le_iff.mp hn; obtain ⟨hv,hc⟩:= max_le_iff.mp hm
    exact widen (((hK n ha).trans (hu n hb m hc)).trans (hK m hv).flip) (by unfold d at *; linarith) (zero_le_one.trans (Q.tight i hi).starts)
omit Q
-- abstract pair facts. Inverse bounded on actual graph input independent x. -
section path
variable {x y:ℕ→ F.Coeff} (h: CauchySeq x)
lemma allowance (h:CauchySeq x) :∃ b:ℝ,0<b ∧∀ n,F.coeffSize (x n)≤ b:=by
    obtain ⟨g,hg⟩:= cauchySeq_tendsto_of_complete h; obtain ⟨b,hb⟩:= ((Size.continuous F|>.continuousAt|>.tendsto|>.comp hg).cauchySeq).isBounded_range|>.bddAbove; refine ⟨max 1 b,lt_of_lt_of_le zero_lt_one (le_max_left ..),fun n=> le_trans (hb (Set.mem_range_self n)) (le_max_right ..)⟩ -- type
lemma merit (h:CauchySeq x) (e:ℝ) (he:0<e):∃ N:ℕ,∀ n≥N,∀ m≥N, F.coeffSize (x n - x m) ≤ e:=by
    let c:= (Fintype.card F.Index : ℝ); have hh:0 ≤ c:=by unfold c; positivity
    obtain ⟨N,hN⟩:= Metric.cauchySeq_iff.mp h (e/(1+c)) (div_pos he (by linarith)); refine ⟨N,fun n hn m hm=>?_⟩; have hx:= hN _ hn _ hm; rw [dist_eq_norm] at hx; exact (Size.le_norm ..).trans ((mul_le_mul (le_add_of_nonneg_left zero_le_one) hx.le (norm_nonneg _) (by change 0≤1+c; linarith)).trans_eq (by field_simp; rfl))
variable {S:ℕ→F.Coeff≃ₗ[ℂ] F.Coeff}(hk:∀ᶠ i in atTop,x i=S i (y i)) {b:ℝ}
lemma succor (hC:NearX (fun i=>(S i).toLinearMap))(hb:0<b)(hS:∀ n v, F.coeffSize v≤ b* F.coeffSize (S n v))(hx:CauchySeq x)(hk:∀ᶠ i in atTop,x i=S i (y i)): CauchySeq y:=by
    obtain ⟨b',hg,hu⟩:= allowance hx; obtain ⟨k,hK⟩:= eventually_atTop.mp hk
    have hh n (hn:k≤n): F.coeffSize (y n)≤ b*b':=by
       apply (hS n _).trans; rw [← hK n hn]; exact mul_le_mul_of_nonneg_left (hu n) hb.le
    apply Metric.cauchySeq_iff.mpr; intro ε hε
    let e:= ε/(4*b); have he:0 < e:=div_pos hε (by positivity); let d:=e/(b*b'); obtain ⟨u,hU⟩:=hC d (div_pos he (mul_pos hb hg)); obtain ⟨v,hV⟩:= merit hx e he
    refine ⟨max k (max u v),fun n hn m hm=> ?_⟩
    obtain ⟨h,hw⟩:=max_le_iff.mp hn; obtain ⟨ha,hb'⟩:=max_le_iff.mp hw; obtain ⟨hv,ht⟩:=max_le_iff.mp hm; obtain ⟨hp,hq⟩:=max_le_iff.mp ht
    rw [dist_eq_norm]; apply ((Size.norm_le ..).trans (hS n _)).trans_lt; rw [map_sub,← hK n h]; let z:= S n (y m); have he' := hh m hv
    have hx: F.coeffSize (x m-z)≤ e:=by
       rw [hK m hv]; have h:F.coeffSize (S m (y m)-z)≤ d *F.coeffSize (y m):= hU m hp n ha _; refine h.trans ((mul_le_mul_of_nonneg_left he' ?_).trans_eq ?_)
       · unfold d; positivity
       unfold d; field_simp
    rw [show x n - S n (y m)= x n - x m+(x m-z) from by unfold z; abel]; apply lt_of_le_of_lt (mul_le_mul_of_nonneg_left ((Size.add ..).trans (add_le_add (hV n hb' m hq) hx)) hb.le); unfold e; field_simp; linarith
end path
include Q
lemma spends {p':∀ m:ℕ,ℕ →F.Coeff}(ht:CauchySeq (p' k))(he:∀ i:ℕ,∀ h:k ≤ i ,∀ᶠ n in atTop,p' i n=(T i h n|>.leanings (W (i+1) n)) (p' (i+1) n))(v:ℕ)(hv:k≤v): CauchySeq (p' v):=by
     induction v,hv using Nat.le_induction with
     | base=>exact ht
     | succ v h ih=>
       apply succor (Ritzy.invests (Q.tight v h) (Q.voyages (v+1) (by omega))) (zero_lt_one.trans_le (Q.tight v h).senior) (fun i x=> (T v h i).hail (W (v+1) i) _) ih (he v h) -- Iiff orientation
lemma hides (v:ℕ)(h:k≤v) (x:ℕ→ F.Coeff)(hx: CauchySeq x): CauchySeq (fun n=> (W v n).g (x n)):=by
    obtain ⟨b,hb,hB⟩:= allowance hx; apply Metric.cauchySeq_iff.mpr; intro ε hε; let a:= p v; have ha:0<a:=zero_lt_one.trans_le (Q.tight _ h).starts; let e:= ε/(4*a); have he:0<e:=div_pos hε (by positivity)
    obtain ⟨K,hK⟩:= merit hx e he; obtain ⟨N,hN⟩:= Q.voyages _ h (e/b) (div_pos he hb)
    refine ⟨max N K,fun n hn m hm=> ?_⟩; obtain ⟨hv,hp⟩:= max_le_iff.mp hn; obtain ⟨ht,hq⟩:= max_le_iff.mp hm; rw [dist_eq_norm]; let X:= (W v n); let Y':= W v m
    have hh : ‖X.g (x m)-Y'.g (x m)‖≤ (e/b*a)*F.coeffSize (x m):=(hN n hv m ht).2 _
    have hz: ‖X.g (x n-x m)‖ ≤ a*e:= (X.toll _).trans (mul_le_mul_of_nonneg_left ((Work.G08.size_core ..).trans (hK n hp m hq)) ha.le)
    change ‖X.g _-Y'.g _‖< _; rw [show X.g (x n)- Y'.g (x m) = X.g (x n-x m) + (X.g (x m)-Y'.g (x m)) from by rw [map_sub]; abel]; apply (norm_add_le ..).trans_lt
    apply lt_of_le_of_lt (add_le_add hz (hh.trans (mul_le_mul_of_nonneg_left (hB m) (by positivity)))); unfold e; field_simp; nlinarith
end Gear
end YM.MergeProof.Matric
#print axioms YM.MergeProof.Matric.Gear.hides
#print axioms YM.MergeProof.Matric.Gear.spends

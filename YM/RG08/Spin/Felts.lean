import YM.RG08.Spin.Suits
/-!
# Rotate test basis with explicit matrix (dynamical twists on actual Exam).
Coordinates agree **within a given weight**, no tail in marked cones.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
noncomputable section
namespace YM.RG08.Spin
open Filter Lattice Wilson Exterior Precision Laurent FreeResolvent Profiles Finset Function Next.Free RG Bloch Stationary Conductor Staffer Reflect UVExt.Paths Work.F08 Push.AbsoluteSums
open Quire Shade Loom Vale Needle Tall Planned.PrimaryIntegral295 Source Source.Drops Labels Summit Scores Door Run Pill Matrix PowerSeries Pivot Carrier Place Scores.Pages
open scoped BigOperators Topology Real ContDiff
open Wings Summit
variable {G:Gauge}{E e r d τ D j t n k m l :ℕ}{R:ℝ}{F:Labels.Frame G d}{H:Hol G} {c : Side}
section
-- scale preserving radial weighted motions
variable (s: Signed)
lemma basin_spin (u v:Plume G d j)(h:∀ X,shadeC u X = shadeC v ((Film.turnIn G d s) ∘ X)) : Labels.tensor s.ortho (basin v)=basin u := by
    apply Next.Foundations.jet_test_ext; intro J k hk; let f i:=Taylor.turn (G:=G) (j:=i) s.ortho⁻¹; let T:=changedJet f J
    have hz t: changedJet f (scaleJet J t) = scaleJet T t := funext fun j=>map_smul ..
    have hx: (fun t=> shady (d:=d) v (WardBin.engineered t (trunk d T)))=(fun t=>shady u (WardBin.engineered t (trunk d J))):= by
       funext t; unfold shady Tensor.diagonal; rw [h]
       apply congr_arg (shadeC v); funext i; exact funext fun j=> Eq.symm (map_smul (f j.val) (t^(j.val+2)) (J j.val))
    change iteratedDeriv k (fun t=> Labels.read (scaleJet J t) (changed f _)) 0=_; simp_rw [eval_changed,hz]
    exact (Parts.archive_read (shade_safe v) hk T).trans (hx ▸ (Parts.archive_read (shade_safe u) hk J).symm)
lemma ladle_sp (H:Hol G) (j d:ℕ) (V W:Shale (Loc G 1) r)(he:Dappled V)(hV:Polished V)(ht:Dappled W)(hW:Polished W)(hv:∀ m:Side,rootSong V m 0=rootSong W m 0∘orderTurn s):
    ladle H V d j=Labels.tensor s.ortho (ladle H W d j):= by
    unfold ladle; rw [dif_pos ⟨he,hV⟩,dif_pos ⟨ht,hW⟩]
    apply Eq.symm; apply basin_spin s; intro X; rw [shade_all,shade_all]; exact congr_arg (fun t:ℝ=> ((↑((j.factorial:ℝ)⁻¹ * t) : ℂ))) (penny_sig s H X _ _ he.toTidy ht.toTidy hV hW hv)
-- ordinary multi-index coefficients only. no E4 cost absorbed from weighting dynamics.
def appoint (p:Cham)(φ:Exam D) := iteratedFDeriv ℝ (cashT p) φ.val 0 (basis ∘ needleT p)
lemma ap_coins (p q:Cham)(D:ℕ) : appoint p (coinsT D q)=if p=q then 1 else 0 := by rw [appoint]; change iteratedFDeriv ℝ _ (beck q) 0 (basis ∘ _) = _; rw [respondsT,needy]; split_ifs <;> simp_all
lemma ap_sl (b:Letter F)(he:0≤R)(ht:d ≤ D)(φ:Exam D) : chant b ht he φ= appoint b.test φ:=rfl
def bandP (k:ℕ): Finset Cham := (rangeT k).filter fun p=> cashT p=k
lemma band_coin (p: Cham) (k:ℕ): p∈bandP k ↔ cashT p=k := by simp only [bandP,Finset.mem_filter,counted]; omega
lemma ap_lp (p:Cham)(hp:cashT p ≤ D) : ∃ L: Exam D→ₗ[ℝ] ℝ, L.toFun=appoint p := by
    let H:=((bareL p hp (show (0:ℝ)≤0 from le_rfl)).toLinearMap).comp (sheet D 0)
    exact ⟨H,rfl⟩
def RimT (D k:ℕ):Submodule ℝ (Exam D):=Submodule.span ℝ (coinsT D '' ((bandP k) : Set Cham))
lemma coinR (p:Cham)(h:cashT p=k): coinsT D p ∈ RimT D k:= Submodule.subset_span ⟨p,(band_coin ..).mpr h,rfl⟩
-- every fixed homogeneous tensor, via PaperT extraction by ap.
lemma papers_T {v:Exam D}(he:v∈PaperT D k)(hp:k ≤ D): v=∑ i∈rangeT k, appoint i v • coinsT D i := by
    induction he using Submodule.span_induction with
    | mem p hp=>
        obtain ⟨p,hp,rfl⟩:= hp; rw [sum_eq_single_of_mem p hp]
        rw [ap_coins,if_pos rfl,one_smul]; intro i _ he; rw [ap_coins,if_neg he,zero_smul]
    | zero=>
        rw [sum_eq_zero]; intro i hi; obtain ⟨L,hl⟩:= ap_lp i (le_trans ((counted i).1 hi) hp); rw [← hl,show L.toFun 0=0 from L.map_zero,zero_smul] -- lemma
    | add x y _ _ hx hy=>
        have hh i (hi:i∈ rangeT k): appoint i (x+y)=appoint i x+appoint i y:= by obtain ⟨L,hl⟩:=ap_lp i (le_trans ((counted i).1 hi) hp); rw [← hl]; exact L.map_add _ _
        nth_rw 1 [hx]; nth_rw 1 [hy]; rw [←sum_add_distrib]; refine sum_congr rfl fun i hi=>?_ ; rw [hh i hi,_root_.add_smul]
    | smul t x hx ih=>
        have hh i (hi:i∈rangeT k): appoint i (t • x)=t * appoint i x := by obtain ⟨L,hl⟩:=ap_lp i (le_trans ((counted i).1 hi) hp); rw [← hl]; exact map_smul L ..
        nth_rw 1 [ih]; rw [Finset.smul_sum]; exact Finset.sum_congr rfl fun i hi=> by rw [hh i hi,smul_smul]
lemma picks_hp (A : Tensor.T E4 ℝ k) (h:Tensor.Sym A) (hi:k≤ D): let v:= mental D k A; v=∑ p∈bandP k, appoint p v • coinsT D p := by
    intro v; refine (papers_T (tensorT A) hi).trans (Eq.symm (sum_subset (filter_subset ..) fun i hi hx=> ?_))
    have he:= mt ((band_coin i k).mpr) hx
    have hg := coeff_diagonal_else A h he; have hb:=DFunLike.congr_fun hg (basis ∘ needleT i)
    rw [show appoint i v=0 from ?_,zero_smul]; apply (mul_eq_zero.mp (show (↑(cashT i).factorial:ℝ)⁻¹ * appoint i v=0 from hb)).resolve_left (by positivity)
lemma twist_pay (q:Cham)(D:ℕ) (hp:cashT q ≤ D) : let v:= twisting s (coinsT D q); v=∑ p∈bandP (cashT q), appoint p v • coinsT D p := by -- p unused
   intro v
   have ht:v.val∈ exactDegree ℝ (cashT q) := by
     refine exact_of_smooth ?_ (fun x t=>?_)
     exact (((beck_cont q).contDiffAt).comp _ (Ortho.motion s.ortho).contDiff.contDiffAt).of_le le_top
     change beck q (Ortho.motion s.ortho (t • x))=_; rw [map_smul,exact_scale (page_poly q)]; rfl
   obtain ⟨V,hV,H⟩:= pure_sym ht; rw [show v=mental D (cashT q) V from ?_] -- form
   exact picks_hp V hV hp
   exact Subtype.ext H
lemma ap_agrees (φ ψ: Exam D)(p:Cham)(hp: Tensor.coeff φ.val (cashT p) 0=Tensor.coeff ψ.val (cashT p) 0): appoint p φ=appoint p ψ:= mul_left_cancel₀ (show ((cashT p).factorial:ℝ)⁻¹≠0 by positivity) (DFunLike.congr_fun hp (basis ∘ needleT p))
lemma twist_eq (φ ψ:Exam D)(hp:Tensor.coeff φ.val k 0=Tensor.coeff ψ.val k 0)(he:k≤ D): Tensor.coeff (twisting s φ).val k 0=Tensor.coeff (twisting s ψ).val k 0 := by
   let A := (Ortho.motion s.ortho).toContinuousLinearEquiv.toContinuousLinearMap
   ext1 i; have h (φ:Exam D) : Tensor.coeff (twisting s φ).val k 0 i= Tensor.coeff φ.val k 0 (A ∘ i):= by
       exact congr_arg ((k.factorial:ℝ)⁻¹ * · : ℝ→ℝ) (DFunLike.congr_fun (Next.Foundations.jets_linear A (((Scores.score D φ).of_le (Nat.cast_le.mpr he)).contDiffAt)) i)
   rw [h,h,hp]
def sails (D:ℕ) : Exam D→ₗ[ℝ] Exam D where
   toFun := twisting s
   map_add' _ _:= rfl
   map_smul' _ _:= rfl
theorem ap_turn (p: Cham)(φ: Exam D)(hp:cashT p ≤ D): appoint p (twisting s φ)=∑ q∈bandP (cashT p), appoint p (twisting s (coinsT D q))*appoint q φ:= by
    let k:=cashT p; let X:=Tensor.coeff φ.val k 0; have hx:Tensor.Sym X:= Tensor.coeff_symm (((Scores.score D φ).of_le (Nat.cast_le.mpr hp)).contDiffAt)
    let u := mental D k X
    have ht: Tensor.coeff u.val k 0=Tensor.coeff φ.val k 0:= coeff_at_diagonal X hx
    have hv: twisting s u=∑ q∈bandP k, appoint q u • twisting s (coinsT D q):= by
       conv_lhs=> rw [show twisting s u=(sails s D) u from rfl, show u=_ from picks_hp X hx hp, map_sum]
       exact sum_congr rfl fun i _=> map_smul ..
    rw [← ap_agrees _ _ p (twist_eq s u φ ht hp), hv]
    obtain ⟨B,hB⟩:= ap_lp p hp; rw [← hB]; change B _ = _; rw [_root_.map_sum]; refine Finset.sum_congr rfl fun i hi=>?_ ; rw [map_smul]; have he:= (band_coin ..).mp hi
    have hh:= ap_agrees u φ i (by rw [he]; exact ht)
    rw [hh, mul_comm]; rfl -- appoint toFun
end
end YM.RG08.Spin

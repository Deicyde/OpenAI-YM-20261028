import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tablet
import YM.AnalyticNext.CONNECTED_ACTIVITY_JETS_E6.Tint



/-!
# Ordered real perturbation markets

 Any-order `Brush` signals buy genuine ordered left derivatives, not
 just commuted chart jets. Keep conservative multiple-up in slots, no
 exponential in area/occurrence count. Needed by V-derivative purchases.
 -/
set_option autoImplicit false
noncomputable section
namespace YM.ConnectedActivityE6.Blaze.March
open Filter Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset MeasureTheory Matrix
open Push Push.AbsoluteSums Precision Exterior Shell Channel Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent SliceRows Mask Tags Progress.StationaryScenes Green Census Work.F03 Animals Control Window Coat Footprint Raw
open Pulse Itinerary     Corona Brush   Tablet   Bid 
open Packets   Poll      Rotation
open scoped Topology InnerProductSpace Matrix.Norms.Frobenius ContDiff BigOperators Classical
variable {G : Gauge} {E D Y : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup D] [NormedSpace ℝ D] {x:E}
variable {c : Side} {j n l k : ℕ} {r q a W d C A b v B: ℝ}

lemma nestle (f : E × ℝ → D) (p : Brush (k+1) B 1 f (x,0)) : Brush k B 1 (fun i=> deriv (fun t:ℝ=> f (i,t)) 0) x := by
  let h := ContinuousLinearMap.inl ℝ E ℝ; let g:= ContinuousLinearMap.inr ℝ E ℝ
  let L:D→L[ℝ] D:= ContinuousLinearMap.id ..; let K:E × ℝ:=g 1
  have hz : ContDiffAt ℝ (↑k) (fderiv ℝ f) (x,0) := p.smooth.fderiv_right (by push_cast; rfl)
  have he (i:E) (hh : DifferentiableAt ℝ f (i,0)) : deriv (fun t:ℝ=> f (i,t)) 0=fderiv ℝ f (h i) K := by
    let v(t:ℝ):=(i,t)
    have hv : HasFDerivAt v g 0 := (show HasFDerivAt (fun _:ℝ=>i) 0 0 from hasFDerivAt_const _ _).prodMk (hasFDerivAt_id _)
    exact ((hh.hasFDerivAt.comp 0 (show HasFDerivAt v g 0 from hv)).hasDerivAt).deriv
  have hK : Brush k B 1 (fun i=> fderiv ℝ f i K) (h x) := by
    refine ⟨hz.clm_apply contDiffAt_const,zero_le_one,fun i hi=> ?_⟩
    have hp := p.order (i+1) (by omega)
    apply le_trans (norm_iteratedFDeriv_clm_apply_const (c:=K) hz (Nat.cast_le.mpr hi))
    have hs : ‖K‖=1:= by unfold K g; simp
    simpa only [normJ, norm_iteratedFDeriv_fderiv,hs,one_mul,one_pow,mul_one] using hp
  have hh:= reading h hK (show ‖h‖≤1 from ContinuousLinearMap.norm_inl_le_one ..)
  rw [mul_one] at hh; apply hh.shimmy; filter_upwards [h.continuous.continuousAt.eventually (show ∀ᶠ y in 𝓝 (h x), _ from p.smooth.eventually (by simp))] with i hi
  exact he i (hi.differentiableAt (by simp))

lemma expands {g : Config G c → ℝ} (l : List (Directions G c)) (t : ℝ) (u : Config G c) :
    leftDerivs g (l.map (fun i=> t • i)) u = t^l.length • leftDerivs g l u := by
  induction l generalizing u with
  | nil => simp
  | cons i l ih =>
    simp only [List.map_cons,List.length_cons]
    simp_rw [leftDerivs, ih]; rw [deriv_fun_const_smul_field]; simp_rw [smul_smul,mul_comm _ t];
    have hh := deriv_comp_mul_left t (fun x : ℝ=> leftDerivs g l (increment u (x • i))) 0
    rw [mul_zero] at hh; rw [hh,smul_smul]; rfl
-- budget on chart slots derived by Brushing all finite-dimensional curves (NO order resetting)
def Ore (P : Config G c) (g : Config G c→ℝ) (v B : ℝ) (k : ℕ) := ∀ (E: Type)
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] (U:E → Config G c) (x:E), U x=P → Mode U x k v → Brush k B 1 (g ∘ U) x

variable {P : Config G c} {g : Config G c → ℝ} {U : E → Config G c}
-- the gain parameter σ = number of movers * oars * threshold
lemma oar (G : Gauge) (k : ℕ) : ∃ Z : ℝ, 0 < Z ∧ ∀ (c:Side) (t:ℝ), 0≤t → ∀ (A: Directions G c), ‖A‖≤t →
    ∀ (E: Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → Config G c) (x:E) (d:ℝ), Mode f x k d →
    Mode (fun i:E × ℝ=> increment (f i.1) (i.2 • A)) (x,0) k (Z*t+d) := by
  obtain ⟨u,hu,hv⟩:= Brush.neighborhood (0:G.Color) (f:=fun i=> G.mat (G.lieExp i)) (k:=k)
      (G.exp_jet.contDiffAt.of_le le_top)
  let H:= k.factorial*u
  let Z := 2*max 1 H
  have hz : 0<max 1 H:= lt_of_lt_of_le zero_lt_one (le_max_left ..)
  refine ⟨Z,mul_pos (by norm_num) hz,fun c t ht A hA E _ _ f x d p => ⟨add_nonneg (by unfold Z; positivity) p.pos,fun i=>?_⟩⟩
  let B:= ContinuousLinearMap.fst ℝ E ℝ; have hB : ‖B‖≤1:= ContinuousLinearMap.opNorm_le_bound _ zero_le_one
    (by intro v; change ‖v.1‖≤_; rw [one_mul]; exact norm_fst_le ..)
  have hh:= reading B (show Brush k (royalty G) d (fun j=>G.mat (f j i)) (B (x,0)) from p.atLink i) hB; rw [mul_one] at hh
  let V := (ContinuousLinearMap.snd ℝ E ℝ).smulRight (A i)
  have hc : Brush k 1 t V (x,0) := by
    refine linearB V ?_ ?_ ht
    · unfold V; simp
    rw [one_mul]; apply ContinuousLinearMap.opNorm_le_bound _ ht; intro v; change ‖v.2 • A i‖≤_; rw [norm_smul,mul_comm t]; gcongr
    · exact norm_snd_le v
    exact (norm_le_pi_norm _ _).trans hA
  let ψ j:=G.lieExp (V j)
  have he : V (x,0)=0 := zero_smul ℝ _
  have hf : Brush k H ((1+(1:ℝ))*t) (G.mat ∘ ψ) (x,0) := hc.pine (he.symm ▸ hv.self_of_nhds)
  apply (links hf hh _ (le_refl _)).climb le_rfl ?_
  apply le_of_eq; unfold Z; ring

lemma explorers [FiniteDimensional ℝ E] (H : Ore P g v B k) (ht : Mode U x k d) (he:U x=P)
    (hO : ∀ (A: Directions G c), ‖A‖≤W → ∀ (E: Type) [NormedAddCommGroup E] [NormedSpace ℝ E] (f : E → Config G c) (x:E) (d:ℝ),
      Mode f x k d → Mode (fun i:E × ℝ=> increment (f i.1) (i.2 • A)) (x,0) k (q+d))
    (l : List (Directions G c)) (hp : d+l.length*q ≤ v) (hq : ∀ i∈l, ‖i‖≤W) (hb : j + l.length ≤ k) :
    Brush j B 1 ((leftDerivs g l) ∘ U) x := by
  induction l generalizing E j d with
  | nil => simp only [List.length_nil, Nat.cast_zero, zero_mul,add_zero] at hp hb
           apply (H E U x he ?_).smaller hb
           exact ⟨ht.pos.trans hp,fun i=> (ht.atLink i).climb le_rfl hp⟩
  | cons A l ih =>
    let V (i:E×ℝ):= increment (U i.1) (i.2 • A)
    have hA := hO A (hq _ (by simp)) E U x d ht
    simp only [List.length_cons,Nat.cast_add,Nat.cast_one] at hb hp
    apply nestle (f:=(leftDerivs g l) ∘ V)
    apply ih hA _ _ (fun i hi=> hq _ (List.mem_cons_of_mem _ hi)) (by omega)
    · simp [zero_smul,he,Work.G07.at_zero_increment]
    nlinarith [hp]
end YM.ConnectedActivityE6.Blaze.March

import YM.OPE.Measuring.Grams
import YM.Push.FINITE_DETECTION.TwoPoint

/-!
# Pair Gram tariff in the weak measuring frames

A bound on the inverse applied to actual labels, without assuming the relative
normalization. First expose a fully nondegenerate two-field limit with both
maps the moving ones on the *same* trajectory. No phase change is involved
in measuring this matrix. Lower slots are included. Then test that matrix
using also the upstream engineering asymptotics on true fixed fields.
This direction is independent of upper prices for the columns of `X`.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Levy
open Set Filter Function Pert Orbits Spec Table Extraction Ward Climb Next.UVStress
open Push.FiniteDetection.Free Maxwell
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical ComplexOrder
set_option backward.privateInPublic true

variable {G:Gauge}{C:Family G}{f:Order}{S:Table C.book}
local notation "L" => C.labels
local notation "Q" => Maxwell.freeTable C.labels

variable (h:Final C f S)(d:ℕ)
def pair (T:Table C.book)(x:Points 2)(u v:S.Field d):ℂ :=
    S.classMoment T (fun _=>d) x ![u,v]
def free2 (u v:(Q).Field d):ℂ := (Q).classMoment Q (fun _ => d) detectors ![u,v]

local notation "ρ" => Maxwell.Free.spin_free C.labels
local notation "σ₀" => Push.FiniteDetection.Kelvin.σ
set_option quotPrecheck false
local notation "a₀" => Table.conj Q (Maxwell.Free.spin_free C.labels) d

-- `σ` is a Signed? Check below.
abbrev reflect (v:(Q).Field d): (Q).Field d:= (Q).mirror ρ d (Signed.mirror timeAxis) (a₀ v)

lemma free_positive (x:(Q).Field d) (hx:x≠0):0<(free2 (C:=C) d x (reflect (C:=C) d x)).re:=by
   let p:=Maxwell.Free.address C.labels d x
   obtain ⟨w,hw⟩:∃ y,Maxwell.observable G d y=p:= Maxwell.Free.address_in C.labels d x
   have hp:p≠0:= fun h=> hx (Maxwell.Free.address_inj C.labels d  (show Maxwell.Free.address C.labels d x=Maxwell.Free.address C.labels d 0 from h.trans (map_zero _).symm))
   have he:=two_detect w (fun h'=>hp (hw.symm.trans (show Maxwell.observable G d w=0 from h')))
   have hq: Maxwell.Free.reflectPol σ₀ (Maxwell.Free.realForm p) = observable G d (Labels.tensor σ₀ (Labels.realBar w)):=by rw [Maxwell.Free.pulls_label,Maxwell.Free.real_eats,hw]
   have ht (y z : (Q).Field d): free2 d (C:=C) y z = disc (fun i:Fin 2=> (⟨d,![y,z] i⟩:Table.Tag Q)) detectors :=rfl
   rw [ht,disc,Maxwell.Free.display]; convert he using 2
   apply DFunLike.congr_arg (Wick.moment G detectors)
   ext1 i; unfold Maxwell.Free.supply reflect
   fin_cases i <;> dsimp
   · exact hw.symm
   rw [Maxwell.Free.address_motion,Maxwell.Free.address_star]; exact hq

variable {ι V : Type*}[AddCommGroup V][Module ℂ V]
def linear₂ (p:MultilinearMap ℂ (fun _:Fin 2=> V) ℂ): V→ₗ[ℂ]V→ₗ[ℂ]ℂ :=
  let B(x y : V):ℂ:=p ![x,y]
  let N(i) (x y:V):= p.toLinearMap ![x,y] i
  have h(v x y): N 0 v y x = B x y:= by unfold N B; rw [MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp
  have g(w x y): N 1 x w y = B x y:= by unfold N B; rw [MultilinearMap.toLinearMap_apply]; congr 1; ext1 i; fin_cases i <;> simp
  LinearMap.mk₂ ℂ B
    (fun x y z=>by simpa only [h] using (N 0 x z).map_add x y)
    (fun a x y=>by simpa only [h] using (N 0 x y).map_smul a x)
    (fun x y z=>by simpa only [g] using (N 1 x y).map_add y z)
    (fun c x y=>by simpa only [g] using (N 1 x y).map_smul c y)

variable (X:Scaling S)(H:FirstExtension h X)
local notation "P" => fun k=> pair (S:=S) d S (X.r k • detectors)
local notation "V'" => (Q).Field

include H
lemma diagram (u v:(Q).Field d) {e:ℝ}(he:0< e) :
   ∀ᶠ k in atTop, ‖P k (X.U k d u) (X.U k d v)- free2 (C:=C) d u v‖ ≤ e := by
     let b i: (Q).Tag:= ⟨d,![u,v] i⟩
     let q(k:ℕ):=scaledPhysical X h.sector.energy k b (fun _=>false) 0
     let F(k:ℕ):=fun z : Points 2=>disc (q k) (X.r k • z)
     let D:=disc (freeWithStress L b (fun _=>false) 0)
     have hj := H.jets 2 0 b (fun _=>false) 0 isCompact_singleton (singleton_subset_iff.mpr detectors_in) he
     filter_upwards [hj] with k hk
     specialize hk detectors rfl
     change ‖iteratedFDeriv ℝ 0 (F k) detectors - iteratedFDeriv ℝ 0 D detectors‖≤e at hk
     rw [show (iteratedFDeriv ℝ 0 (F k) detectors - iteratedFDeriv ℝ 0 D detectors)= iteratedFDeriv ℝ 0 (F k-D) detectors by ext; simp, norm_iteratedFDeriv_zero,Pi.sub_apply] at hk
     have eq:P k (X.U k d u) (X.U k d v) = F k detectors :=by
       unfold F; rw [show q k=fun i: Fin 2=> (⟨d,X.U k d (![u,v] i)⟩:S.Tag) from rfl]
       unfold pair disc useAt
       exact DFunLike.congr_arg _ (funext fun i=>by fin_cases i <;> rfl)
     dsimp only at eq; rw [eq]; apply hk

-- a TWO slot, not just a many-spectator detector
def panel (k:ℕ) : (V' d)→ₗ[ℂ] (V' d)→ₗ[ℂ] ℂ where
  toFun v:= (((linear₂ (S.classMoment S (fun _ : Fin 2=>d) (X.r k • detectors))).comp (X.U k d).toLinearMap) v).comp (X.U k d).toLinearMap
  map_add' x y:=by rw [map_add]; rfl
  map_smul' r x:=by rw [map_smul]; rfl
def target: V' d →ₗ[ℂ] V' d →ₗ[ℂ] ℂ := linear₂ ((Q).classMoment Q (fun _=>d) detectors)

lemma limits (u v:V' d): Tendsto (fun k=>panel d X k u v) atTop (𝓝 (target (C:=C) d u v)):= by
    apply Metric.tendsto_nhds.mpr
    intro ε he; filter_upwards [diagram h d X H u v (half_pos he)] with k hk
    rw [dist_eq_norm]; exact hk.trans_lt (half_lt_self he)

set_option maxHeartbeats 1500000 in
lemma joint {E:Type*}{l:Filter E}{n:E→ℕ}{x y:E→V' d}{x₀ y₀:V' d}(hn:Tendsto n l atTop)(hx:Tendsto x l (𝓝 x₀))(hy:Tendsto y l (𝓝 y₀)):
     Tendsto (fun i=>panel d X (n i) (x i) (y i)) l (𝓝 (target d (C:=C) x₀ y₀)) :=by
       refine YM.Dash.arcing (W:=fun i=> (panel d X (n i) (x i)).toContinuousLinearMap) (X:=LinearMap.toContinuousLinearMap (target (C:=C) d x₀)) (?_) hy
       refine YM.Dash.fit_plane _ _ (fun p : V' d=> ?_)
       let A:= (LinearMap.applyₗ (R:=ℂ) p : (V' d →ₗ[ℂ] ℂ) →ₗ[ℂ] ℂ)
       exact YM.Dash.arcing (YM.Dash.fit_plane (fun i=> A.comp (panel d X (n i))) (A.comp (target (C:=C) d)) (fun u : V' d=> (limits h d X H u p).comp hn)) hx

omit H in
lemma reflect_limit {E:Type*}{l:Filter E}{x:E→V' d}{y}(hx:Tendsto x l (𝓝 y)): Tendsto (reflect (C:=C) d ∘ x) l (𝓝 (reflect d y)) :=by
     have he : Continuous (reflect (C:=C) d) := by
        let A: V' d →ₗ[ℝ] V' d := {
             toFun v:= reflect d v
             map_add' _ _:=by unfold reflect; rw [map_add,map_add]
             map_smul' r v:=by
                 change reflect d (r • v)=r • reflect d v
                 unfold reflect
                 rw [← Complex.coe_smul,← Complex.coe_smul,LinearMap.map_smulₛₗ]
                 simp }
        apply A.continuous_of_finiteDimensional
     exact he.continuousAt.tendsto.comp hx

-- Inverse *quadratic* test with the conjugation implemented separately (no loss from an unknown price on moving exteriors).
private lemma norm_unit: ∃ c:ℝ,0<c ∧ ∀ᶠ n in atTop, ∀ x:V' d, ‖x‖=1 → c ≤ ‖panel d X n x (reflect (C:=C) d x)‖ :=by
       let c(i:ℕ):ℝ:=1/(i+1)
       let Y (i n:ℕ):=∃ x: V' d, ‖x‖=1 ∧ ‖panel d X n x (reflect d x)‖ < c i
       by_contra! hf
       have he(i):∃ n, i ≤ n ∧ Y i n:=Filter.frequently_atTop.mp (hf (c i) (div_pos zero_lt_one (by positivity))) i
       choose g hL x hp hh using he
       obtain ⟨y,-,q,hq,hy⟩:=IsCompact.tendsto_subseq (isCompact_closedBall (0:V' d) 1) (x:=x) (fun i=>mem_closedBall_zero_iff.mpr (by exact (hp i).le))
       have hpos:0<‖target (C:=C) d y (reflect d y)‖:=by
          have h1:=tendsto_nhds_unique hy.norm (tendsto_const_nhds.congr (fun i=> (hp (q i)).symm):Tendsto (fun i=> ‖(x ∘ q) i‖) atTop (𝓝 1))
          have hy:y ≠ 0:=norm_ne_zero_iff.mp (h1.trans_ne one_ne_zero)
          rw [norm_pos_iff]
          exact fun H => (free_positive d y hy).ne' (congr_arg Complex.re H)
       apply hpos.not_ge
       have hg:Tendsto g atTop atTop:=tendsto_atTop_mono (f:=id) hL tendsto_id
       exact le_of_tendsto_of_tendsto' ((joint h d X H (hg.comp hq.tendsto_atTop) hy (reflect_limit d hy)).norm) (tendsto_one_div_add_atTop_nhds_zero_nat.comp hq.tendsto_atTop) (fun i=>(hh _).le)

section
omit H
private lemma quadratic (n:ℕ) (x:V' d) (a:ℝ) : panel d X n ((a:ℂ) • x) (reflect (C:=C) d ((a:ℂ) • x))= ((a:ℂ)^2) * panel d X n x (reflect d x):=by
     have he: a₀ ((a:ℂ) • x)=(a:ℂ) • a₀ x:=by rw [LinearMap.map_smulₛₗ]; simp
     unfold reflect; rw [he, map_smul, map_smul, LinearMap.smul_apply,map_smul]; simp only [smul_eq_mul,pow_two,mul_assoc]
end
lemma norm_test: ∃ c:ℝ,0<c ∧ ∀ᶠ n in atTop, ∀ x:V' d, ‖x‖^2 ≤ c* ‖panel d X n x (reflect (C:=C) d x)‖ :=by
     obtain ⟨c,hc,hk⟩:= norm_unit h d X H
     refine ⟨_, inv_pos.mpr hc, hk.mono fun n hn x=>?_⟩
     rcases eq_or_ne x 0 with rfl|hx
     · simpa only [norm_zero,zero_pow (show 2 ≠ 0 from by decide)] using mul_nonneg (inv_pos.mpr hc).le (norm_nonneg _)
     let e:ℝ:=‖x‖⁻¹; have hp:0<e:= inv_pos.mpr (norm_pos_iff.mpr hx)
     have he:e*‖x‖=1:=inv_mul_cancel₀ (norm_ne_zero_iff.mpr hx)
     have h₁ : ‖(↑e:ℂ)‖=e:= (Complex.norm_real ..).trans (Real.norm_of_nonneg hp.le)
     have ht := hn ((e:ℂ) • x) (by rw [norm_smul,h₁,he])
     rw [quadratic d X,norm_mul,Complex.norm_pow,h₁] at ht
     apply (le_inv_mul_iff₀ hc).2
     calc _ ≤ e^2 * ‖panel d X n x (reflect d x)‖ * ‖x‖^2:=mul_le_mul_of_nonneg_right ht (sq_nonneg _)
          _ = _:=by change ‖x‖⁻¹^2 * _ * _ = _; field_simp [(norm_ne_zero_iff.mpr hx)]

end YM.OPE.Levy

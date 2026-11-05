import YM.UVExtension.Strata.Sand
set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Strata
open Filter Function Metric Set RG Lattice Pressure Wilson Precision Exterior Push.AbsoluteSums Finset ConnectedActivityE6
open Push Bloch Next.Fluctuations Blaze Channel SliceRows Work.E03 Work.F03 Reward Laurent Tree
open Push SectorMeasure
open Pressure.Stores Pressure.Tube Scroll
open Progress.StationaryScenes Green Control Window Census Pulse Itinerary Coat Poll Pond AnalyticBridge.RelativeLogdet
open Blaze.Frond Steady
open scoped BigOperators Topology InnerProductSpace ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n c f L :Side}{S:StepData c f} {ι α β κ:Type}{v:Filter ι}
variable {qq: Filter κ} {T:ι→Tube G S} {w:ℝ} {X:Teller G}
    {Q: ConnectedActivityE6.Target G X} {U:Target.Order G w} {R:ι→ Rep G f}
    {s δ q η r W C B V f' a g u D' ψ Y ζ:ℝ} {k l:ℕ} {χ:Chi}
namespace Polish
open Matrix MeasureTheory WithLp Shield
open Span Oriented Vine
variable {H:∀ i,Cash w s q L Q U C (T i) (R i)} {A b N r d f' Z:ℝ} (p: Span.Score v T H k l χ A b u B N r d f' V Z)
section motion
variable {F:Forest S.ratio} (Δ:ι→Directions G f)

def apartF (i : ι)(P:Coat (T i) F): F.Slice G→ Air f G:= fun y=> WithLp.toLp 2 (Vine.well (P.wrapY y))
variable (i:ι)(P:Coat (T i) F)
lemma account (F:F.Slice G)(z : Air _ G): Score.rent (c:=c) (R i).beta (P.wrapY F) ((P.wrapY F).atmos z)= (gStep (R i).beta)⁻¹ • (z-apartF i P F):=rfl
include H
lemma shoes (hs:P.x=s)(hK:P.width=U.K) : Measurable (apartF i P):=by
    let N:= H i; have h:ShellAccess S G P.x w P.width U.γ:=by rw [hs,hK]; exact N.laws.data.access
    have ht:= Shield.compassBro (Y:=id) (V:=fun _ : F.Slice G=> P.V) (N.laws.intake.ready) measurable_const P measurable_id h 0
    let L : Directions G f→ₗ[ℝ] Air f G:={ toFun:=fun z=> WithLp.toLp 2 (stand z),map_add':=fun _ _=>rfl,map_smul':=fun _ _=>rfl }; exact L.toContinuousLinearMap.measurable.comp ht.1
omit H
end motion
variable [NeBot v]
include p
private lemma all_norm {J:Type} [Fintype J] (b:ℝ)(hp:0≤b)(M:Matrix J J ℝ)(h:∀ i j, |M i j| ≤ b): ‖M‖ ≤ Real.sqrt ((Fintype.card J:ℝ)*( (Fintype.card J:ℝ)*b^2)):=by
   rw [Matrix.frobenius_norm_def, ← Real.sqrt_eq_rpow]; apply Real.sqrt_le_sqrt
   trans ∑ _i:J,∑ _j:J,b^2
   · apply sum_le_sum; intro i _; apply sum_le_sum; intro j _; simpa only [Real.norm_eq_abs,Real.rpow_two] using! (pow_le_pow_left₀ (abs_nonneg _) (h i j) 2)
   simp [nsmul_eq_mul]
-- all J.PDA compact. Uses paid Ledger uniform & ground spectral.
lemma presidents : ∃ d r y:ℝ, 0≤d∧0<r∧0<y∧∀ (F:Forest S.ratio)(i) (P:Coat (T i) F), P.width=U.K →P.x=s→ P.manifest→ P.relating∈ Minaret.Town d r∧ Bottom P.relating⁻¹ y:=by
    let v:= U.ample; let σ:= v⁻¹/2; have hv:0<v:= zero_lt_one.trans_le U.f.hQ; have hσ:0<σ:=half_pos (inv_pos.mpr hv); let V:=payE U.eta U.gap v (tubularPrice G L); let G₀:=Tubular f G; let D:= Real.sqrt ((Fintype.card G₀:ℝ)*( (Fintype.card G₀:ℝ)*(1+|V|)^2)); use D, σ, (1+|V|)⁻¹
    refine ⟨Real.sqrt_nonneg _,hσ,(by positivity),fun F i P hK hs hM=>?_⟩
    have ht:= ((H i).laws.data.localP F P hs hK hM).sails; have he:= ht.scale.weather.1.le; have hp:=increase (ht.scale.mate P.shutter) he ((le_abs_self V).trans (le_add_of_nonneg_left zero_le_one))
    have hh:= ht.scale.ground_C P.shutter ht.cap
    refine ⟨⟨⟨mem_closedBall.mpr (by rw [dist_zero_right]; exact all_norm p (1+|V|) (by positivity) _ (only_price hp.1 le_rfl)),ht.fullC.isHermitian⟩,hh⟩,?_⟩
    exact Control.lower_inverse hp (le_refl 0) (by positivity) ht.fullC.isHermitian hh hσ.le (Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr ht.fullC.det_pos.ne'))
lemma salary (hu:0≤u) : ∃ d:ℝ, 0≤d∧∀ (F:Forest S.ratio)(i:ι)(P:Coat (T i) F), P.width=U.K→ P.x=s→ P.χ=χ→ P.manifest →∀ y, ‖apartF i P y‖≤d:=by
    obtain ⟨d,r,φ,hd,hL,hp,h⟩:= p|>presidents
    let v:=U.ample; let J:=Coat.Target c f G; let K:=Tubular f G; let M:=payE U.eta U.gap v (tubularPrice G L); let b:= (Fintype.card J:ℝ) * (U.indexPay*|Z|); let s':= (Fintype.card K:ℝ)*(M*b); let x:= Real.sqrt ((Fintype.card K:ℝ)*s'^2)
    refine ⟨x,Real.sqrt_nonneg _,fun F i P hU hs ht hr y=>?_⟩
    let Q':=P.wrapY y; have he:= ((H i).laws.data.localP F Q' hs hU hr).sails
    have ha:Mode (fun _:ℝ=>P.V) 0 k u:= ⟨hu,fun i=>a_oneB G _ hu⟩
    have hv j:|stand (bar Q' 0) j| ≤ Z:= ((p.tech ℝ _ F i Q' 0 hs ht hU hr rfl ha).2 j).bound
    have hx:0≤ U.indexPay:= he.signs.le; let w:= he.scale; have hh:= w.weather
    have hk j: |leanB Q' j|≤b:= by
        unfold leanB Matrix.mulVec dotProduct; apply (Finset.abs_sum_le_sum_abs ..).trans; refine le_trans (sum_le_sum (g:=fun _=>U.indexPay *|Z|) (fun j' _=>?_)) ?_
        · rw [abs_mul]; exact mul_le_mul (Control.only_price he.matrix.1 w.eta.le j' j) ((hv j').trans (le_abs_self _)) (abs_nonneg _) hx
        simp only [sum_const,nsmul_eq_mul,card_univ]; rfl
    have hV j:|apartF i P y j| ≤ s':=by
        unfold apartF well; simp only [WithLp.ofLp_toLp, Pi.neg_apply, abs_neg]; unfold Matrix.mulVec dotProduct; apply (Finset.abs_sum_le_sum_abs ..).trans; refine le_trans (sum_le_sum (g:=fun _=> M*b) (fun j' _=>?_)) ?_
        · rw [abs_mul]; exact mul_le_mul (Control.only_price (w.primal Q'.shutter).1 (by linarith only [hh.1]) j' j) (hk j') (abs_nonneg _) w.disc
        simp only [sum_const,nsmul_eq_mul,card_univ]; rfl
    refine le_of_sq_le_sq ?_ (Real.sqrt_nonneg _); rw [EuclideanSpace.real_norm_sq_eq]; unfold x; rw [Real.sq_sqrt (by positivity)]; refine le_trans (Finset.sum_le_sum (g:=fun _=>s'^2) fun j _=>?_) ?_
    · rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hV j) 2
    simp only [sum_const,nsmul_eq_mul,card_univ]; rfl

section skew
omit p [NeBot v]
variable {A X:Type}[MeasurableSpace A] {J:Type}[Fintype J] {p': A→Poll.Body J}
def curtain (hp:Measurable p'): A× Poll.Body J≃ᵐ A × Poll.Body J:=
    { toFun := fun i=> (i.1,i.2-p' i.1)
      invFun := fun i=> (i.1,i.2+p' i.1)
      left_inv := fun i=> Prod.ext rfl (sub_add_cancel ..)
      right_inv := fun i=>Prod.ext rfl (add_sub_cancel_right ..)
      measurable_toFun:= measurable_fst.prodMk (measurable_snd.sub (hp.comp measurable_fst))
      measurable_invFun:=measurable_fst.prodMk (measurable_snd.add (hp.comp measurable_fst)) }
lemma preservationT (hp:Measurable p')(μ:Measure A)[SFinite μ]: MeasurePreserving (curtain hp) (μ.prod volume) (μ.prod volume):=by
   have h:= MeasurePreserving.id μ; apply h.skew_product (g:=fun x y=> y-p' x) (measurable_snd.sub (hp.comp measurable_fst)); filter_upwards with i; simp_rw [sub_eq_add_neg]; exact (measurePreserving_add_right volume (-(p' i))).map_eq
end skew
-- includes factors Warp.Current
variable {F:Forest S.ratio}(i:ι)(P:Coat (T i) F)(hs:P.x=s)(hw:P.width=U.K)(ht:P.χ=χ)(hm:P.manifest)
variable {W: Type} [NormedAddCommGroup W][NormedSpace ℝ W]
def wound (s: F.Slice G × Air f G): Air f G:= (Coat.gStep (R i).beta)⁻¹ • (s.2-apartF i P s.1)
def quilt (s:F.Slice G × Air f G):= Wick.lint (R i).beta (Fintype.card (Tubular f G))* lens₀ P.relating (wound (R:=R) i P s)
def shiftV (g : F.Slice G × Air f G→ W) (x : F.Slice G × Air f G) := (quilt (R:=R) i P x) • g (x.1,wound (R:=R) i P x)
include p hs hw hm
lemma pedals (g:F.Slice G × Air f G→ W)(hp:Integrable g ((F.order G).prod P.dice)):
    Integrable (shiftV (R:=R) i P g) ((F.order G).prod volume) ∧ (∫ x,g x ∂((F.order G).prod P.dice))= ∫ x,shiftV (R:=R) i P g x ∂((F.order G).prod volume):=by
   have he:=(H i).laws.data; have hx:=(he.localP F P hs hw hm).sails.fullC; have hn:=(H i).laws.intake.positive; have hq:= shoes (H:=H) i P hs hw
   let K:=Wick.tether P.relating (R i).beta g; have ht : shiftV (R:=R) i P g= K ∘ (curtain hq) := rfl
   have hV:= preservationT hq (F.order G);
   rw [ht]; exact ⟨hV.integrable_comp_emb (curtain hq).measurableEmbedding|>.2 ((Wick.gear _ P.relating hx hn g).mp hp), (Wick.axle _ P.relating hx hn g).trans (hV.integral_comp' K).symm⟩
end Polish
end YM.UVExtension.Strata

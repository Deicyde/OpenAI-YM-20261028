import YM.OPE.Nesting.Quantified

/-! Bounded masses on **joint** geometries (not assuming independent smearing
or absolute continuity wrt flat volume). Coefficient system is kept unchanged
from the unaveraged context. Intersections of finite-horizon collars are open;
each such request fits its collar eventually throughout the relative shape
town. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting
open Orbits Orbits.Reader Function Filter Extraction Set Table Measures Menu Atom MeasureTheory Finset TopologicalSpace
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical

namespace Tree
lemma Tapered.pricePositive {t:Tree}{s:t.Inner→ℝ}{β r:ℝ}(h:t.Tapered r β s)(a)(ha:0<a)(v:t.Inner):0<t.ratios a s v :=by induction t generalizing a r with
  | bud=> cases v
  | fork n f hi=> rcases v with u | ⟨j,q⟩
                  · cases u; exact div_pos h.1 ha
                  exact hi j (h.2.2 j) _ h.1 _
lemma Tapered.pay_nonneg {n:ℕ}{f:Fin n→Tree}{s:(fork n f).Inner→ℝ}{r β:ℝ}(h:Tapered _ r β s)(w ε m):0 ≤ toll w ε m s:= mul_nonneg (Real.rpow_nonneg h.1.le _) (prod_nonneg (fun i _=>Real.rpow_nonneg (h.pricePositive _ one_pos _).le _))
lemma Tapered.pay_both_nonneg {n:ℕ}{f:Fin n→Tree}{s:(fork n f).Inner→ℝ}{r β:ℝ}(h:Tapered _ r β s)(w ε m d):0 ≤ bothToll w ε m d s:=mul_nonneg (h.pay_nonneg ..) (sum_nonneg fun p _=>pow_nonneg (h.pricePositive _ one_pos (Sum.inr p)).le _)
end Tree
open Tree
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(h:Services C F S)

section Raw
variable {L J:Type}[Fintype J]{l:Filter L}{T:L→ℝ}(hT:Tendsto T l atTop)[l.NeBot]
variable {n:ℕ}{f:Fin n→Tree}{ε:ℝ}{a:(fork n f).Inner→ℝ}{z:Envelope L (fork n f)}
       {s:L→(fork n f).Inner→ℝ}{y:L→J→E4} (v:(fork n f).Leaf→S.Tag)(w:J→S.Tag)
       (he:0<ε)(hs:∀ v,RateIs l T (fun i=>s i v) (-a v))(ht:(fork n f).ordered 0 a)
       (h₀:∑ v,a v=1)(hg:Regular l T (fork n f) 0 a z)
       (hp:Intervals l T 0 z y)(hy:Kept l T 0 y)
include R h hT he hs ht h₀ hg hp hy
private lemma raw_pricewise (r:L→Viewers U):
       ∀ᶠ i in l, ‖duet (spectator U (r i)) (Tree.profile (z i)) v (y i) w‖ ≤ toll (wages v) ε 0 (s i):=by
    let k:= Tree.cost (fork n f) 0 a (wages v); let P:= Menu.raw z v
    have h₁:=Measures.interval_comp hp (fun _:Unit=>(fork n f).topSeat) id
    obtain ⟨-,hd⟩:=Fusion.tariff U R hT h (fork n f) _ _ _ v hg
    have hx:RateLE l T (delta U R P 0 (Tree.center z) r w y) k:=by
       exact ((hd.tested w y 0 r _ _ hy (interval_comp hp (fun _:Unit=> (fork n f).topSeat) id) hp le_rfl le_rfl hg.nonneg) |>.mono (by rw [mul_zero,add_zero]; exact sub_le_self _ (by have hf:= hg.nonneg; positivity)))
    let g(c:Cut R 0)(i:L):=P.charge R c.1 c.2 (Tree.center z) i * soloView U R _ c.2 (z i|>anchor) (r i) w (y i)
    refine Limits.base_charge (s:=s) hT v hs ht h₀ he (RateLE.congr (RateLE.mono (RateLE.add hx (RateLE.sum (S:=Finset.univ) (f:=g) hT (fun q _=>?_)) hT) (by rw [zero_mul,sub_zero])) (Eventually.of_forall (fun i=> (sub_add_cancel .. |>.trans (Menu.raw_view ..)))))
    have hu(q:Cut R 0):q.fst.val=0:= by omega
    have hv:=pulse_single U R (s:=r) (C:=C) (w:=w) hT h q.2 h₁ hy (le_refl 0) (le_refl 0)
    exact ((hd.output q.1 q.2).mul hv).mono (by simp [hu]; exact le_rfl)
end Raw

section JointLaw
variable {K Y:Type}[MeasurableSpace K][MeasurableSpace Y]
lemma measure_eval (f:K→ℂ)(g:Y→ℂ)(x:K→Y){μ:Measure K}(V:Set Y)(C B:ℝ)
    (hf: Integrable f μ) (hx:AEMeasurable x μ)(hneg:∀ᵐ s ∂μ,f s≠0 → x s∈V)
    (hg:Measurable (V.indicator g))(hp:∀ᵐ s ∂μ,f s≠0 → ‖g (x s)‖ ≤ C) (hc:0≤ C)(hB:∫ s, ‖f s‖ ∂μ ≤ B): let u:= fun s=> f s*g (x s); Integrable u μ ∧ ‖∫ s,u s ∂μ‖ ≤ B*C:=by
       let u:=fun s:K=> f s*g (x s); change Integrable u μ ∧ ‖∫ s,u s ∂μ‖ ≤ B*C
       have hms : Integrable (fun s=> ‖f s‖ * C) μ:= hf.norm.mul_const C
       have he: AEStronglyMeasurable u μ:= (hf.1.mul ((hg.comp_aemeasurable hx).aestronglyMeasurable)).congr <| hneg.mono (fun s hs=> by
          by_cases hf:f s=0; · change f s*_ = f s*_; rw [hf,zero_mul,zero_mul]
          exact congr_arg (f s *·) (V.indicator_of_mem (hs hf) _))
       have h':∀ᵐ s ∂μ,‖u s‖ ≤ ‖f s‖ * C:=hp.mono fun s h=> by
          by_cases h':f s=0; · simp [u,h']
          exact (norm_mul_le ..).trans (mul_le_mul_of_nonneg_left (h h') (norm_nonneg _))
       exact ⟨hms.mono' he h',(norm_integral_le_of_norm_le hms h').trans (by rw [integral_mul_const]; exact mul_le_mul_of_nonneg_right hB hc)⟩
variable {n:ℕ}{f:Fin n→Tree}{T:K→ℝ}
variable {M η ε δ:ℝ}(hM:0≤M)(hη:0<η)(hε:0<ε)
       (v:(fork n f).Leaf→S.Tag)
structure CoefIntegral (v:(fork n f).Leaf→S.Tag)(m:ℕ)(c:R.channels m)(D:(fork n f).Inner→ℕ)
       (B ε:ℝ)(s:(fork n f).Inner→ℝ)(z:Envelope K (fork n f))(f:K→ℂ)(μ:Measure K):Prop where
   base: Integrable (fun i=> f i * Kernel.output U R (z i) v c) μ
   compounded:Integrable (fun i=> f i * Kernel.chord U R (z i) v c D) μ
   ask: ‖∫ i,f i*Kernel.output U R (z i) v c ∂μ‖ ≤ B*toll (wages v) ε m s
   dual: ‖(∫ i,f i*Kernel.output U R (z i) v c ∂μ)-(∫ i,f i*Kernel.chord U R (z i) v c D ∂μ)‖ ≤ B * bothToll (wages v) ε m D s
include h hM hη hε
lemma coefficient_joint {n:ℕ}{p:Fin n→Tree} (v:(fork n p).Leaf→S.Tag) (m:ℕ)(c:R.channels m)(D:(fork n p).Inner→ℕ):
    ∀ᶠ r:ℝ in 𝓝[>]0, ∀ (s:(fork n p|>.Inner)→ℝ),Tapered _ r 1 s → ∀ (μ:Measure K)(B:ℝ)(q:K→ℂ)(z:Envelope K (fork n p)), Integrable q μ→ (∫ i, ‖q i‖ ∂μ) ≤ B→ AEMeasurable z μ→
       (∀ᵐ i ∂μ, q i≠0→Accept r M η s (z i)) → CoefIntegral U R v m c D B ε s z q μ:=by
    let t:=fork n p; let g₁(x:Tree.Plot t):=Kernel.output U R x v c; let g₂(x:Tree.Plot t):=Kernel.chord U R x v c D; let g₀(x:Tree.Plot t):=g₁ x-g₂ x
    let V:=(Kernel.aperture U R t m D) ∩ {z| orbitMargin R.port m (Tree.profile z) (z|>anchor)}
    have he:IsOpen V:= Kernel.stencil U R .. |>.inter (Kernel.collar_open U R m)
    have hc:ContinuousOn g₁ V:= fun x hx=>(Kernel.output_smooth U R v c hx.2).continuousAt.continuousWithinAt
    have h':ContinuousOn g₂ V:= fun x hx=>(Kernel.chord_smooth U R v c D hx.1).continuousAt.continuousWithinAt
    have hm:Measurable (V.indicator g₁):=by
       convert hc.measurable_piecewise (continuousOn_const (c:=(0:ℂ))) he.measurableSet using 1; ext i; by_cases h:i∈V <;> simp [Set.indicator,Set.piecewise,h,g₀]
    have hm':Measurable (V.indicator g₀):= by
       convert (hc.sub h').measurable_piecewise (continuousOn_const (c:=(0:ℂ))) he.measurableSet using 1; ext i; by_cases h:i∈V <;> simp [Set.indicator,Set.piecewise,h,g₀]
    filter_upwards [Limits.coe_power U R h hM hη hε v m c D] with r h s hx μ B f z hf hB hz hl
    let a:=bothToll (wages v) ε m D s; let b:= toll (wages v) ε m s
    have ht := hl.mono (q:=fun i=> f i≠0→ z i∈V) fun i hi hg=>⟨(h s (z i) (hi hg)).2.1,(h s (z i) (hi hg)).1⟩
    have hvs (g:Tree.Plot t→ℂ){c:ℝ}(hh:∀ᵐ i ∂μ,f i≠0→‖g (z i)‖ ≤ c)(hm:Measurable (V.indicator g))(hc:0≤c):= measure_eval f g z V c B hf hz ht hm hh hc hB
    obtain ⟨h₁,h₁'⟩:=hvs g₁ (hl.mono fun i hi hf=>h _ _ (hi hf) |>.2.2.1) hm (hx.pay_nonneg ..)
    obtain ⟨h₀,h₀'⟩:=hvs g₀ (hl.mono fun i hi hf=>h _ _ (hi hf) |>.2.2.2) hm' (hx.pay_both_nonneg ..)
    have h₂: (fun i=>f i*g₂ (z i))=(fun i=>f i*g₁ (z i)-f i*g₀ (z i)):=funext fun i=>by dsimp only [g₀]; rw [mul_sub,sub_sub_cancel]
    have hp: Integrable (fun i=>f i*g₂ (z i)) μ:= h₂ ▸ h₁.sub h₀
    refine ⟨h₁,hp,h₁',(?_ : ‖ (∫ i, f i*g₁ (z i) ∂μ) - (∫ i, f i*g₂ (z i) ∂μ)‖ ≤ _)⟩
    rw [← integral_sub h₁ hp]; exact (show (fun i=> f i * g₀ (z i)) = (fun i=> f i * g₁ (z i) - f i * g₂ (z i)) from funext (fun i=>mul_sub ..)) ▸ h₀'

variable {J:Type}[Fintype J](w:J→S.Tag)(hδ:0<δ)
include R hδ
lemma raw_wave:∀ᶠ r:ℝ in 𝓝[>]0,∀ (s:(fork n f).Inner→ℝ)(z:Tree.Plot (fork n f))(y:J→E4),Accept r M η s z → Buffer z y δ → ∀ q:Viewers U, ‖duet (spectator U q) (Tree.profile z) v y w‖ ≤ toll (wages v) ε 0 s:=by
     let t:=fork n f; let V:=(t.Inner→ℝ)× Tree.Plot t × (J→E4)
     let P r(x:V):=Accept r M η x.1 x.2.1 ∧ Buffer x.2.1 x.2.2 δ
     let Q(r:ℝ)(x:V):=∀ q:Viewers U, ‖duet (spectator U q) (Tree.profile x.2.1) v x.2.2 w‖ ≤ Tree.toll (wages v) ε 0 x.1
     letI : Nonempty t.Inner:=⟨Sum.inl ()⟩
     refine (refine_geometry (P:=P) (Q:=Q) ?pu).mono (fun r hr s z y h he=>hr (s,z,y) ⟨h,he⟩)
     intro x ψ hψ ht hr; let s:=Prod.fst ∘ x; let z:=Prod.fst ∘ Prod.snd ∘ x; let y:=Prod.snd ∘ Prod.snd ∘ x
     obtain ⟨χ,h_c,hχ,T,a,h₀,hT,hs,hg,ha⟩ := t.find_layers (z:=z) (s:=s) (tendsto_id (α:=ℝ)|>.mono_left ht) (hr.mono fun i h=>⟨h.1.levels,h.1.relative⟩) hM hη
     obtain ⟨hp,hy⟩:=Limits.buffer_stage (z:=z) (y:=y) hT hδ ((hr.mono fun i hi=>hi.2).filter_mono hχ)
     exact ⟨χ,h_c,hχ,universalize <| raw_pricewise (y:=y) U R h hT v w hε hs ha h₀ hg hp hy⟩

end JointLaw
end YM.OPE.Nesting

import YM.UVExtension.Wick.Dome

set_option autoImplicit false
noncomputable section
namespace YM.UVExtension.Wick
open Function Lattice RG Pressure Pressure.Stores Pressure.Tube Tree Wilson Finset Matrix
open Push Push.AbsoluteSums Precision Exterior Next.Fluctuations SectorMeasure Oriented Work.E03
open Bloch Laurent Work.F03 Progress.StationaryScenes Bid
open ConnectedActivityE6 Blaze Shell Channel SliceRows Control Window Census Green Mask Pulse Itinerary Coat Footprint Raw Poll Pond
open Blaze Scroll Vine Polar Frond Corona Brush Foramen Gate Tablet Strokes Quill
open Packets Art Silica Shield Eider Flux Hues Rotation Matter
open Lamppost MeasureTheory Set Filter
open scoped Topology BigOperators Matrix.Norms.Frobenius ContDiff ENNReal InnerProductSpace Classical
variable {G : Gauge} {c f L : Side} {S : StepData c f} {T : Tube G S} {F : Forest S.ratio} {P : Teller G} {Z : ChartRatio G}
variable (X : Coat T F) {R : RG.Rep G f} {u v s a : ℝ} {z : Air f G} {Y : Config G c}
open Animals Reserves
variable {ι : Type} [Fintype ι]
variable {x y γ W μ δ e b B C u D d r q' A v' g w b' Y' n:ℝ} {K l j : ℕ} {χ:Chi} {Q : YM.ConnectedActivityE6.Target G P}
    {o : Target.Order G W} {H : Cash W x μ L Q o a T R} {V : ι→ Juice G f}
namespace Bower
variable (N : Bower Q o L S.patch μ χ A b x j K u B C r d n) (hS:Stamp T) (hF : Festa Q L H V w g)

variable {X} (hX:X.x=x)(hm:X.manifest)(hc:X.χ=χ)(hr:X.width=o.K)

section paid
variable (P : Teller G) (Q : YM.ConnectedActivityE6.Target G P) (L:Side) (W μ:ℝ) (o:Target.Order G W) (A b:ℝ) (χ:Chi)
lemma forestation {e γ : ℝ} (hi:0<e) (hp: Q.rate+e<γ) (hK:γ<0) (hg:Q.rate ≤γ) (n₀ j k:ℕ) {B u r d n:ℝ→ℝ} {C:ℝ}
    (hm:0<μ)(ht:0 ≤ C) (hr:Rate G L 0 r) (hv:Rate G L 1 n) (hb:Rate G L 0 B) : ∃ (C':ℝ) (Z:ℝ→ℝ), Rate G L 0 Z ∧ ∀ᶠ x in atTop, ∀ (D:Patch),
    0≤ n x → ∀ p:Bower Q o L D μ χ A b x j k (u x) (B x) C (r x) (d x) (n x), 0≤ Z x ∧
     ∀ (c f:Side) (S:StepData c f) (T:Tube G S) (A':Rep G f) (a:ℝ) (H:Cash W x μ L Q o a T A'), Stamp T→ ∀ hD:D=S.patch,
      ∀ (ι:Type) [Fintype ι], Fintype.card ι=n₀ → ∀ (v:ι→ Juice G f) (g:ℝ), let t:=betaF G x L^e; ∀ (H':Festa Q L H v g t) (z:Vines ι), ∀ hz:z∈ parade (betaF G x L) t,
        Nonempty (Lush (hD ▸ p) H' z hz (Z x) ((stalk Q hg hK).costs L μ (z none).re x C')):= by
  obtain ⟨y₀,hy,hY⟩:= trunkfit G L; obtain ⟨a',ha,hA⟩:= Brush.neighborhood (k:=j) 0 ((show ContDiff ℝ (↑j) Complex.exp from Complex.contDiff_exp).contDiffAt); obtain ⟨z',hz,hZ⟩:= Brush.neighborhood (k:=j) 1 (Real.contDiffAt_log.mpr (by norm_num))
  let D:= 1+(j.factorial:ℝ)*a'; have hD:0<D:=by unfold D; positivity
  let Ω x:=(1+D*(1+24*(j.factorial*z'+j.factorial*z'))*2)*(B x*2^k)
  let X x:=1+r x+D*(1+48*n x)
  have hv : Rate G L 1 X:= (((Rate.const 1|>.add hr).weaken zero_le_one).add ((((Rate.const 1|>.weaken zero_le_one)).add (hv.mul_left _)).mul_left D))
  obtain ⟨s,hs,hS⟩:= conical hv j; have hη:0≤ C+y₀+s:=by positivity
  have hhP := (stalk Q hg hK).pay_for L hm hη
  obtain ⟨R,hR,F⟩:= fugue j; obtain ⟨M,hM,H⟩:= climaxes j
  let q:=R + R*M; have hr: 0≤R:=zero_le_one.trans hR; have hq:R≤q:=le_add_of_nonneg_right (mul_nonneg hr hM.le)
  refine ⟨C+y₀+s,Ω,hb.mul_right (2^k)|>.mul_left _,?_⟩
  filter_upwards [hY,hS, indulgent P L Q γ e q n₀ hi (by linarith only [hp]),hhP,Rate.power (G:=G) (L:=L)|>.below hK 1 zero_lt_one,
    Rate.power (G:=G) (L:=L)|>.below Q.stop (1/2) (by norm_num), permits G L] with
    x hY' hS h hl hT hE hv D' hx p; let t:=betaF G x L^e; unfold Ω
  have hu:0≤ Ω x:=by unfold Ω; have he:=p.roof; positivity
  refine ⟨hu,fun c f S T Rm bm H' hYk hD' ι _ hk v g H₀ z hz=>?_⟩
  let β':= z none; let ε:= β'.re; have hv' := (marching z).1 hz; let Z:=oneV H₀ z hz
  have he:= H'.laws.data.funds.length_eq
  subst D'
  obtain ⟨Ξ⟩:Nonempty (Utopia Z j (u x) (d x) (r x) C χ):= (p.granted _ _ S T _ _ Z hYk rfl).1
  let f i:= (H₀.kin i _ hv'.1).some
  let f' i:= ((p.granted _ _ S T _ _ (f i) hYk rfl).1).some
  have ht := h c _ S T Rm _ hk Ξ.flair (fun i=>(f' i).flair) Ξ.uses (fun i=> (f' i).uses); rw [abs_of_nonneg (le_trans hr hq)] at ht
  have hb:1≤ r x:=Ξ.active
  refine launching p hYk H₀ z hz (hv c _ S _ he hv'.1|>.2) Ξ f' R M y₀ s q hg hK (hl ε hv'.1.1.le) ht z' a' hy hx (hR.trans hq) hr (le_add_of_nonneg_left hr) hq F H ((le_abs_self _).trans hE) ((le_abs_self _).trans hT) ?_ (fun F X hh A q=> hY' c _ S T F X hh he _ _ _ hv'.1) hA.self_of_nhds hZ.self_of_nhds
  intro P hP
  have hh:1≤ (P.shares:ℝ) := by exact_mod_cast hP
  apply le_trans _ (hS P.shares hP)
  apply pow_le_pow_left₀ (by positivity)
  change 1+r x + D*(1+48* n x * P.shares) ≤ _; apply le_trans _ (mul_le_mul_of_nonneg_right (le_abs_self _) (Nat.cast_nonneg _)); unfold X; nlinarith only [hh,hD,hb]

end paid
end Bower
end YM.UVExtension.Wick

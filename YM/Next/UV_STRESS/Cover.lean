import YM.Next.UV_STRESS.Layout


/-!
# Estimates on the joint pairs used by Grill

Reflection diffs of products. The upper limits are on the same extraction used
in the rooted cost, not changing it to pass the anti-pairs.
-/

set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Extraction Around Wilson Cells Lattice OS
open scoped Topology BigOperators
variable {G : Gauge} {C : Family G} {h k N p n : ℕ} {F : Extraction.Order} {d : ℕ}

private def wayOut (t i : ℕ) : Cover := fun _ => (t:ℤ)*i

private def blockPair {n m} (x : Fin n → Cover) (y : Fin m → Cover) (t i j : ℕ) :=
    Fin.append (fun k => x k + wayOut t i) (fun k => y k + wayOut t j)

private lemma gaps {n m} (x : Fin n → Cover) (y : Fin m → Cover) (hx : Injective x) (hy : Injective y)
    (i j : ℕ) (h : i<j) : ∀ᶠ t in atTop, Injective (blockPair x y t i j) := by
  have he : ∀ᶠ t : ℕ in atTop,∀ a b,x a 0+wayOut t i 0<y b 0+wayOut t j 0 := by
    refine eventually_all.mpr (fun a => eventually_all.mpr (fun b => ?_))
    filter_upwards [eventually_gt_atTop ((x a 0-y b 0).natAbs)] with t ht
    unfold wayOut
    have hf : x a 0-y b 0 < (t:ℤ) := by omega
    nlinarith [(show (i:ℤ)<j by exact_mod_cast h)]
  filter_upwards [he] with t ht b c
  unfold blockPair
  refine Fin.addCases ?_ ?_ b
  · intro b; refine Fin.addCases ?_ ?_ c
    · intro c he; simp at he; rw [hx he]
    intro c he; simp only [Fin.append_left, Fin.append_right] at he
    exact ((ht b c).ne (congr_fun he 0)).elim
  intro b; refine Fin.addCases ?_ ?_ c
  · intro c he; simp only [Fin.append_left, Fin.append_right] at he
    exact ((ht c b).ne (congr_fun he.symm 0)).elim
  intro c he; simp at he; rw [hy he]

namespace Maker
variable (P : Maker C F h d)

private def theme (v : Fin n → Entitled C d) (x : Fin n → Cover) (k N p t i : ℕ) : Config G (C.side N p) → ℝ :=
    P.sunset v k N p (fun j => x j + wayOut t i)
private def orig (v : Fin n→Entitled C d) (x : Fin n→Cover) (k N p t i : ℕ) (U : Config G (C.side N p)) :=
    Grid.tiny k (C:=C) (fun j => (v j).val) x N p (wayOut t i) U

private def receipt {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) (A G : Ω → ℝ) (b : ℝ) :=
    Integrable A μ ∧ Integrable G μ ∧ |(∫ x,A x∂μ)-(∫ x,G x∂μ)| ≤ b

private lemma receipt_sub {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω) {b c : ℝ} {A B J G : Ω → ℝ}
    (h : receipt μ A J b) (p : receipt μ B G c) : receipt μ (A-B) (J-G) (b+c) := by
  obtain ⟨h,hj,hf⟩ := h; obtain ⟨p,hg,hr⟩ := p
  refine ⟨h.sub p,hj.sub hg,?_⟩
  simp_rw [Pi.sub_apply, integral_sub h p,integral_sub hj hg]; rw [sub_sub_sub_comm]
  exact (abs_sub ..).trans (add_le_add hf hr)

private lemma layout_hyp (v : Fin n→Entitled C d) (w : Fin n→Entitled C d) (x : Fin n→Cover) (y : Fin n→Cover)
    (H : C.Makes) (hs : CellHyp C F) (hx : Injective x) (hy : Injective y) :
    ∃ A : ℝ,0≤A ∧ ∀ k i j : ℕ, i<j → ∀ᶠ t in atTop, F.late fun N p =>
      let V := fun u : Config G (C.side N p) => P.theme v x k N p t i u*P.theme w y k N p t j u
      let U := fun u : Config G (C.side N p) => (orig v x h N p t i u*orig w y h N p t j u).re
      let μ := law G (C.side N p) (C.beta N p)
      Integrable V μ ∧ Integrable U μ ∧ |(∫ u,V u ∂μ)-(∫ u,U u ∂μ)| ≤ costHint k * A := by
  let z := Fin.append v w
  obtain ⟨A,hA,HX⟩ := P.precise z H hs
  refine ⟨A,hA,fun k i j hj => ?_⟩
  filter_upwards [gaps x y hx hy i j hj] with t ht
  let X := blockPair x y t i j
  obtain ⟨B,-,hB⟩ := HX k
  have he : ∀ᶠ p in atTop, Injective ((wrap (C.side h (F.per p))) ∘ X) := F.per.cofinal.eventually (sparse C.S h X ht)
  unfold Extraction.Order.late
  rw [Extraction.Order.fused,Extraction.Order.late] at hB
  filter_upwards [hB,he] with p hm hp
  filter_upwards [hm] with N hh
  let G₁ := fun u => P.theme v x k (F.mesh N) (F.per p) t i u*P.theme w y k (F.mesh N) (F.per p) t j u
  let G₂ := fun u => orig v x h (F.mesh N) (F.per p) t i u*orig w y h (F.mesh N) (F.per p) t j u
  let μ := law G (C.side (F.mesh N) (F.per p)) (C.beta (F.mesh N) (F.per p))
  have hu : G₁=P.sunset z k (F.mesh N) (F.per p) X := by
    funext g; simp only [Fin.append_left,Fin.append_right,G₁,theme,sunset,z,X,Fin.prod_univ_add,blockPair]
  let r j := location C.S h (F.mesh N) (F.per p) (X j)
  have hR : G₂ = fun a => ∏ j,C.seen (z j).val (r j) a := by
    funext a; simp only [Fin.append_left,Fin.append_right,G₂,z,r,X,blockPair,Fin.prod_univ_add,orig,Grid.tiny]
  have hu' : Integrable (paint G₁) μ := hu.symm ▸ (hh X).1.integrable _
  have hr : Integrable G₂ μ := hR.symm ▸ C.integrableR (fun i => (z i).val) r
  have hG u : (paint G₁ u).re=G₁ u := rfl
  refine ⟨hu'.re,hr.re,?_⟩
  have hc : ‖(∫ u, paint G₁ u ∂μ)-(∫ u, G₂ u ∂μ)‖ ≤ costHint k * A := by rw [hu,hR]; exact (hh X).2.2 hp
  change |(∫ u, G₁ u ∂μ)-(∫ u,(G₂ u).re ∂μ)| ≤ _
  calc
    _ = |((∫ u, paint G₁ u ∂μ)-(∫ u,G₂ u ∂μ)).re| := by rw [Complex.sub_re,show (∫ u,G₁ u∂μ)=(∫ u,paint G₁ u∂μ).re from integral_re hu',
      show (∫ u,(G₂ u).re∂μ)=(∫ u,G₂ u∂μ).re from integral_re hr]
    _ ≤ _ := (Complex.abs_re_le_norm _).trans hc

-- All proofs on the pair readings of a common Covering, with genuine measurable
-- bounded witnesses. No uniform bounds claimed on the physical-cutoff primaries.
include P in
theorem patrons (H : C.Makes) (hs : CellHyp C F) (v : Fin n → C.book.Token) (w : ∀ i, (v i).1 ≤ d)
    (hw : Grid.plain (C:=C) v) (x : Fin n→ Cover) (hx : Extraction.Order.grid C h x∈generic _) :
    ∃ Y : Grid.Covering (C:=C) h v x,Y.Works h v x F := by
  let X (i : Fin n) : Entitled C d := ⟨v i,w i,hw i⟩
  let s := Signed.mirror timeAxis
  let L (i) := variant (X i) (s,false)
  let y := s.act ∘ x
  have hy (N p t i : ℕ) (u : Config G (C.side N p)) : Grid.flash h v x N p t i u= orig X x h N p t i u-orig L y h N p t i u := by
    rfl
  have ht : Injective x := by
    intro i j hz
    exact generic_conf _ hx (congr_arg (C.S.gridPoint h) hz)
  have hp : Injective y := (Signed.act_injective _).comp ht
  let f := P.theme X x; let g := P.theme L y
  obtain ⟨A,_,hA⟩ := P.precise X H hs
  obtain ⟨B,_,hB⟩ := P.precise L H hs
  choose a ha hv using hA
  choose b hb hu using hB
  obtain ⟨u,_,hh⟩ := P.layout_hyp X X x x H hs ht ht
  obtain ⟨r,_,hr⟩ := P.layout_hyp X L x y H hs ht hp
  obtain ⟨p,_,hP⟩ := P.layout_hyp L X y x H hs hp ht
  obtain ⟨l,_,hL⟩ := P.layout_hyp L L y y H hs hp hp
  let Y : Grid.Covering h v x := ⟨fun k N p t i => f k N p t i-g k N p t i,fun k => a k+b k,
    fun k => costHint k*(u+r+p+l),by simpa using cost_clears.mul_const (u+r+p+l)⟩
  refine ⟨Y,⟨fun k t j => ?_,fun k i j he => ?_⟩⟩
  · have hf (Z : Fin n→Entitled C d) c (s : Fin n→Cover) (i : ℕ×ℕ) : Interior univ (paint (P.theme Z s k i.1 i.2 t j)) →
        (∀ q, |P.theme Z s k i.1 i.2 t j q| ≤ c) → Measurable (P.theme Z s k i.1 i.2 t j) := fun h _ =>
      Complex.continuous_re.measurable.comp h.borel
    have he : ∀ᶠ i : ℕ × ℕ in F.fuse, Measurable (Y.plots k i.1 i.2 t j) ∧ ∀ q, |Y.plots k i.1 i.2 t j q| ≤ Y.reserve k := by
      filter_upwards [hv k,hu k] with i hi hh
      specialize hi (fun p => x p + wayOut t j); specialize hh (fun p => y p + wayOut t j)
      refine ⟨(hf X (a k) x i hi.1 hi.2.1).sub (hf L (b k) y i hh.1 hh.2.1),fun q =>
        (abs_sub ..).trans (add_le_add (hi.2.1 q) (hh.2.1 q))⟩
    exact he
  filter_upwards [hh k i j he,hr k i j he,hP k i j he,hL k i j he] with t H₁ H₂ H₃ H₄
  unfold Extraction.Order.late at *
  filter_upwards [H₁,H₂,H₃,H₄] with n h₁ h₂ h₃ h₄
  filter_upwards [h₁,h₂,h₃,h₄] with N h₁ h₂ h₃ h₄
  -- arithmetic of four integrable rows
  let m := F.mesh N; let w := F.per n
  let μ := law G (C.side m w) (C.beta m w)
  let T (i) := Y.plots k m w t i
  let U i := Grid.flash h v x m w t i
  let V₁ := f k m w t; let V₂ := g k m w t
  let G₁ := orig X x h m w t; let G₂ := orig L y h m w t
  have he (z : Config _ _) : U i z * U j z =
      (G₁ i z * G₁ j z - G₁ i z * G₂ j z) - (G₂ i z*G₁ j z - G₂ i z*G₂ j z) := by
    change Grid.flash _ _ _ _ _ _ _ _ * Grid.flash _ _ _ _ _ _ _ _=_
    rw [hy,hy]; dsimp [G₁,G₂]; ring
  have hw (z : Config _ _) : T i z * T j z =
      (V₁ i z*V₁ j z-V₁ i z*V₂ j z) - (V₂ i z*V₁ j z-V₂ i z*V₂ j z) := by
    change (V₁ _ z - V₂ _ z)*(V₁ _ z - V₂ _ z)=_; ring
  have ht : receipt μ (fun z => T i z*T j z) (fun z => (U i z * U j z).re) (costHint k*(u+r+p+l)) := by
    -- group charges; pay actual real integrability
    simp_rw [he,hw,Complex.sub_re]
    let δ := costHint k
    have A' : receipt μ (fun z => V₁ i z * V₁ j z) (fun z => (G₁ i z * G₁ j z).re) (δ*u) := h₁
    have B' : receipt μ (fun z => V₁ i z * V₂ j z) (fun z => (G₁ i z * G₂ j z).re) (δ*r) := h₂
    have C' : receipt μ (fun z => V₂ i z * V₁ j z) (fun z => (G₂ i z * G₁ j z).re) (δ*p) := h₃
    have D' : receipt μ (fun z => V₂ i z * V₂ j z) (fun z => (G₂ i z * G₂ j z).re) (δ*l) := h₄
    rw [show costHint k*(u+r+p+l)=δ*u+δ*r+(δ*p+δ*l) from by unfold δ; ring]
    exact receipt_sub μ (receipt_sub μ A' B') (receipt_sub μ C' D')
  exact And.right (And.right ht)
end Maker
end YM.Next.UVStress

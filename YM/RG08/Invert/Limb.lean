import YM.RG08.Invert.Sap
/-!
 # gauge-to-tree linear potential (site map), orientation support,
   all unmodified Korea. `Al` absent.
-/
set_option autoImplicit false
set_option linter.unnecessarySeqFocus false
set_option linter.unusedVariables false
noncomputable section
namespace YM.RG08.Invert
open Function Filter Lattice Wilson Exterior Precision Laurent Next.Free Next.Free.Flight RG RG.Supply Bloch Input Matrix
open Planned.PrimaryIntegral295 Carrier
open Stationary Analysis FreeResolvent Tree UVExt.Paths Reflect Work.F08
open scoped BigOperators Topology Real Classical Matrix ContDiff
variable {G:Gauge}{i j k t r:ℕ}{L c f:Side}{κ:KernelChoices}

-- *same* varphi in any usage from repeated trees; budget paid even if analytic lifts ask again.
def turnsCost (G: Gauge)(v:Patch)(κ:KernelChoices)(X:Repeated v.L)(σ:ℝ): ℝ:= if h:0<σ then (turn_fee G v X κ σ h).choose else 0
lemma turnsCost_pay (G:Gauge)(v:Patch)(κ:KernelChoices)(X:Repeated v.L){s:ℝ} (h:0<s): 0≤turnsCost G v κ X s:= by rw [turnsCost,dif_pos h]; exact (turn_fee G v X κ s h).choose_spec.1
-- variants rooted
structure Frosty (P: Patch)(κ:KernelChoices)(x:Repeated P.L)(U: Cross P.L (TypeFace 1) (TypeFace 1))(T:Cross P.L (Loc G 0) (Loc G 1)): Prop where
   hw:Whole T
   honest : ∀ (c f:Side) (i: f.val=c.val*P.L.val),
      let S:=linked P κ c f i
      T.acts c=repackM (unitSplit G S 0) (Equiv.refl _) (patron G (straighten S (x.forest S.ratio) (installed S.ratio U)))
lemma enquire (G:Gauge)(P:Patch)(κ: KernelChoices)(x:Repeated P.L)(U: Cross P.L (TypeFace 1) (TypeFace 1))(h:Whole U):∃ S: Cross P.L (Loc G 0) (Loc G 1), Frosty P κ x U S:= by obtain ⟨s,M,hS,hp⟩:=h; obtain ⟨w,hw,H⟩:= (turn_fee G P x κ s hS).choose_spec.2 U _ hp; exact ⟨w,⟨⟨_,_,hS,hw⟩,H⟩⟩
variable {P:Patch}{x:Repeated P.L}{U V: Cross P.L (TypeFace 1) (TypeFace 1)}{T Z:Cross P.L (Loc G 0) (Loc G 1)}
lemma Frosty.unique (h:Frosty P κ x U T)(hv:Frosty P κ x U Z): T=Z:= bank_injective h.hw.safe hv.hw.safe (fun i=>(h.honest i (i*P.L) rfl).trans (hv.honest i (i*P.L) rfl).symm)
lemma Frosty.comparison (he:Frosty P κ x U T) {σ A:ℝ} (hv:0<σ)(h:U.strip σ A):T.strip σ (turnsCost G P κ x σ*A):=by obtain ⟨w,hw,H⟩:= (turn_fee G P x κ σ hv).choose_spec.2 U _ h; rw [he.unique (Z:=w) ⟨⟨_,_,hv,hw⟩,H⟩,turnsCost,dif_pos hv]; exact hw
lemma Frosty.law (S:StepData c f){U:Cross S.ratio.count (TypeFace 1) (TypeFace 1)}{T:Cross S.ratio.count (Loc G 0) (Loc G 1)}{x:Repeated S.patch.L}(h:Frosty S.patch S.kernel x U T): installed S.ratio T=patron G (straighten S (x.forest S.ratio) (installed S.ratio U)):= by
    ext i j; rw [installed, Matrix.submatrix_apply]; erw [h.honest c f S.sizes];
    let R:=patron G (straighten S (x.forest S.ratio) (installed S.ratio U)); change R ((unitSplit G S 0).symm (unitSplit G S 0 _)) j=_; rw [Equiv.symm_apply_apply]
private lemma minus_t (S:StepData c f)(F:Forest S.ratio)(U V:Matrix (Body 1 f) (Body 1 c) ℝ): straighten S F (U-V)= straighten S F U-straighten S F V:= by
    apply matrix_eq; intro p; funext j; rw [books, sub_mulVec,Matrix.mulVec_sub _ (_*ᵥp)]; rw [_root_.map_sub, sub_mulVec,Pi.sub_apply,Pi.sub_apply,books,books]; abel
private lemma cargos (A:StepData c f)(X: Repeated A.ratio.count)(U V:Cross A.ratio.count (TypeFace 1) (TypeFace 1))(he:Whole U)(hp:Whole V)(G:Gauge):
    let f p:= repackM (unitSplit G A 0) (Equiv.refl _) (patron G (straighten A (X.forest A.ratio) (installed A.ratio p)))
    f (minusRows U V) = f U-f V:=by
    intro p; unfold p; rw [show installed A.ratio (minusRows U V)=installed A.ratio U-installed A.ratio V from ?_,minus_t]; swap; · unfold installed; rw [he.less hp]; rfl
    have hx {P Q : Matrix (Body 0 f) (Body 1 c) ℝ}: patron G (P-Q)=patron G P-patron G Q:= by
       rw [tensor_same,tensor_same,tensor_same];ext i j; unfold tensor; simp only [Matrix.of_apply, Matrix.sub_apply]; split <;> simp_all -- unspecified sides
    rw [hx];rfl
lemma Frosty.sub (h:Frosty P κ x U T)(hv:Frosty P κ x V Z)(he:Whole U)(hp:Whole V): Frosty P κ x (minusRows U V) (minusRows T Z):= by
    refine ⟨h.hw.minus hv.hw,fun c f i=> ?_⟩; intro S
    rw [h.hw.less hv.hw,h.honest c f i,hv.honest c f i]
    exact (cargos S x U V he hp G).symm

-- path synchronized to oriented sigma conventions; Supplies in Drifts windows. Local formal U adapter. Prices=before/after-block through Quilt and `turnsCost`.
abbrev contour (X:Chain)(G:Gauge)(m N:ℕ): Cross (X.S.block m) (Loc G 0) (Loc G 1):= (enquire G (X.patch m) X.kernel (X.trees m) (X.A₀ N m) (X.az_whole ..)).choose
lemma contour_l (X:Chain)(G:Gauge)(m N:ℕ): Frosty (X.patch m) X.kernel (X.trees m) (X.A₀ N m) (contour X G m N):= (enquire _ _ _ _ _ (X.az_whole ..)).choose_spec
open Drift Wings
variable {I:Type}{u:I→Windows}{Y:Chain} {K:KPrices Y.kernel}{g:KGate K}{Q:Lending G Y.kernel}{δ:Prism G Y.kernel g Q i}{p:G.ColorIndex}{j':ChartRatio G}{V: Quilt Y.kernel.penalty g.w}
local notation "α"=> V.alpha
lemma contour_shot (hx:Circuit δ p j' u)(he:Plays u V)(hp:Weighed (Launch.farY Y (u:=u)) (fun i=> turnsCost G (Y.patch i.i) Y.kernel (Y.trees i.i) (α (Y.J (i.i+1)) (Y.J i.i)))) : RowBoth (menu (u:=u) Y) (chop Y (1/104)) (fun i:Wings u 1=> contour Y G i.i i.N) (fun i=> contour Y G i.i i.M) (fun i=> α (Y.J i.up.i) (Y.J i.i)):= by
    obtain ⟨C,hC,Hc⟩:= minor_rails hx he; have hw := (hp.transfer (toLaunch (u:=u) (k:=1))).times hC
    have hz i := (Hc i).1
    refine ⟨⟨_,hw,fun i=>?_⟩,⟨_,hw,fun i=>?_⟩, ⟨_,hw,fun i=>?_⟩⟩
    · rw [Pi.one_apply,mul_one]; exact Frosty.comparison (contour_l ..) (V.ap ..) (hz i|>.high)
    · rw [Pi.one_apply,mul_one]; exact Frosty.comparison (contour_l ..) (V.ap ..) (hz i|>.low)
    let w := Frosty.sub (contour_l Y G i.i i.N) (contour_l Y G i.i i.M) (Y.az_whole ..) (Y.az_whole ..)
    rw [Pi.mul_apply, mul_assoc]; exact w.comparison (V.ap ..) (hz i|>.mov)
end YM.RG08.Invert

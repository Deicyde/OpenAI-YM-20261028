import YM.RG08.Cell.Colour

/-!
# Compare cover covariance lines between UV supplies. Cost uses the proven Flat precision
difference; no Frobenius matrix argument on an unbounded side & no actual gap limit.
-/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Cell
open Stationary Function Matrix Lattice Exterior Precision RG Tree Wilson Laurent Bloch Finset RG08.Rows RG08.Flat Pert.Bulk RG08.Packets RG08.Line
open scoped Matrix BigOperators Topology Classical ENNReal
variable {G : Gauge} {P : Patch} {K : KernelChoices} {n m : Side}

/-- Shape furnished before comparing cutoff. -/
structure Warm (G : Gauge)(K : KernelChoices)(P:Patch)(b:Bed)(σ p:ℝ): Prop where
  bill:Tagged σ p (warm P K G b) (cellLine P K G b)
  invert n : let S:=habitat P K n; let M:= NativeLine S G b
             (∀ x,onTree (green S) (M*ᵥ x)) ∧ (∀ x,onTree (green S) x → M*ᵥ (linePrecision G S b *ᵥ x)=x) ∧ M.transpose=M

variable {p q θ η ε : ℝ}

theorem warm_at (G : Gauge)(K : KernelChoices)(Q : MapPrices)(j : ℕ): ∃ η :ℝ,0<η ∧ η≤1 ∧ ∃ post:Side→ℝ,(∀ i,0≤post i) ∧ ∀ P:Patch,P.Branches K G→ P.J=j→∀ b:Bed,b.metric.strip (Q.α j) (Q.Ω j) → ∀ u D,(∀ n,Floor b u n (Q.η j) D)→ Warm G K P b η (post P.L) := by
  obtain ⟨η,h,he,p,hp,H⟩:= preheat G K Q j; refine ⟨η,h,he,p,hp,fun P ha hi b hb u d hf=>?_⟩; obtain ⟨hr,hT⟩:=H P ha hi b hb u d hf; exact ⟨hr,fun n=>hT n (n*P.L) rfl⟩

-- repack colored production stencil (tile of proven `changeRow`)
def ink (G : Gauge)(P : Patch)(b b':Bed):= tile P.L (color G (changeK b b'))

lemma ink_invoice (G:Gauge)(P:Patch)(K:KernelChoices){L : ℝ} (b b':Bed)(h:RowCost ε 1 (changeK b b') L)(hp:0≤L)
    (hr: b.metric.strip θ q)(hr':b'.metric.strip θ q)(ht:0≤θ)(hq:0≤q)
    (hs:0≤η)(hk:η ≤ P.L.val * ε) : Tagged η (Real.exp (8*η)*L) (ink G P b b') (fun n=> let S:=habitat P K n; repackM (unitSplit G S 1) (unitSplit G S 1) (patron G (quadratic b (n*P.L)-quadratic b' (n*P.L)))):= by
  exact tile_tagged P.L _ P K rfl (color_tagged G (changeRow h hp hr hr' ht hq)) hs hk

def allowance (G : Gauge)(P:Patch)(p:ℝ):ℝ:= (Fintype.card (Co P.L (Loc G 1)):ℝ)^2*p^2*Real.exp (8*1)

lemma earn_grid (G : Gauge)(K:KernelChoices)(P : Patch)(b b' : Bed)(h : Warm G K P b η p)(ht : Warm G K P b' η p)
    {τ π D₂ δ δ' ε u q : ℝ} {m m':Clip}(hT:∀ n,Floor b m n δ π)(_hT':∀ n,Floor b' m' n δ' D₂)
    (hg:RowCost ε 1 (changeK b b') u)(hu:0 ≤ u)(hr:b.metric.strip τ q)(hr':b'.metric.strip τ q)(hτ:0≤τ)(hq:0≤q)(he: 0 ≤ θ)(hθ:θ≤η)(hp:θ≤1)(hx:θ≤P.L.val*ε):
    Priced θ (allowance G P p*u) (warm P K G b' - warm P K G b):= by
  let κ:= P.L
  let r:= warm P K G b; let t:= warm P K G b'
  let ξ:= ink G P b b'
  have hA:= h.bill.mono hθ le_rfl; have hB:=ht.bill.mono hθ le_rfl
  have hV := ink_invoice G P K b b' hg hu hr hr' hτ hq he hx
  let E (n:Side) : Funds (Co n (Co P.L (Loc G 1))) := let S:=habitat P K n; repackM (unitSplit G S 1) (unitSplit G S 1) (patron G (quadratic b (n*P.L)-quadratic b' (n*P.L)))
  have hY: Tagged θ (allowance G P p*u) (Pert.Bulk.bind (Pert.Bulk.bind t ξ) r) (fun n=> cellLine P K G b' n* (E n)* cellLine P K G b n) := by
    have ht:0≤p:= hA.pos
    refine ((hB.mul hV he).mul hA he).mono le_rfl ?_
    calc _ ≤ Fintype.card (Co P.L (Loc G 1))*(Fintype.card (Co P.L (Loc G 1))*(p*(Real.exp (8*1)*u))*p) := by gcongr
         _ ≤ _:= by unfold allowance; apply le_of_eq; ring
  have ha n : cellLine P K G b' n* (E n)* cellLine P K G b n=cellLine P K G b' n-cellLine P K G b n:=by
    let s:=habitat P K n
    let M₁:= NativeLine s G b; let M₂:= NativeLine s G b'; let X₁:=linePrecision G s b; let X₂:=linePrecision G s b'
    obtain ⟨h1,h2,h3⟩:= h.invert n
    obtain ⟨h4,h5,h6⟩:= ht.invert n
    have h7:X₁.transpose=X₁:=by unfold X₁ linePrecision Precision.K; rw [← patron_star,Matrix.transpose_add,Matrix.transpose_smul]; simp only [transpose_mul,transpose_transpose,(hT _).symmetric.1,Matrix.mul_assoc]
    have h8 : M₂*X₂*M₁=M₁:=by refine perVec fun w=>?_ ; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,h5 _ (h1 _)]
    have h9 : M₂*X₁*M₁=M₂:=by
      have H:M₁*X₁*M₂=M₂:=by refine perVec fun w=>?_ ; rw [← Matrix.mulVec_mulVec,← Matrix.mulVec_mulVec,h2 _ (h4 _)]
      have ht:= congr_arg Matrix.transpose H
      rw [transpose_mul,transpose_mul,show M₂ᵀ=M₂ from h6, show M₁ᵀ=M₁ from h3,h7, ← Matrix.mul_assoc] at ht; exact ht
    rw [native_paid,native_paid]
    let z:=unitSplit G s 1
    unfold E
    change repackM z z M₂ * repackM z z (patron G _)*repackM z z M₁=_
    erw [← repack_multiply,← repack_multiply] -- direction args?
    have he : patron G (quadratic b (n*κ) - quadratic b' (n*κ)) = X₁-X₂ := by unfold X₁ X₂ linePrecision; rw [ink_sub,ink_add_general,ink_add_general,add_sub_add_right_eq_sub]
    rw [he, Matrix.mul_sub, Matrix.sub_mul, h9,h8]; rfl
  let s := warm P K G b' - warm P K G b
  have hρ:= hB.sub hA he
  have hη : s=Pert.Bulk.bind (Pert.Bulk.bind t ξ) r := by
    refine readahead (s:=sizes) (t:=sizes) (M:=fun n=>cellLine P K G b' (sizes n)-cellLine P K G b (sizes n)) ?_ hρ.row hY.row he he ?_ ?_ -- m? s t
    · exact increasing
    · exact fun n=>hρ.seen (sizes n)
    intro n; simpa only [ha] using hY.seen (sizes n)
  change Priced θ _ s
  exact hη.symm ▸ hY.toPriced
end YM.RG08.Cell

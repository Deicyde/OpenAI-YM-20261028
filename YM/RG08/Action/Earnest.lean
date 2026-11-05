import YM.RG08.Action.Wrought
/-!
# Use any pre-certified root turn with mean data, no inter-cutoff lift
 prices tapped in repeated estimates. -/
set_option autoImplicit false
noncomputable section
namespace YM.RG08.Staffer
open Filter MeasureTheory
open Function Analysis Tree Lattice RG Stationary Wilson Precision Exterior Laurent FreeResolvent Profiles Finset Next.Free
open PertExtension.Series.Tested PertExtension.Series.Radial Matrix Reflect Conductor Bloch UVExt.Paths Work.F08 Push.AbsoluteSums
open scoped BigOperators Topology Real ContDiff Classical Matrix.Norms.Frobenius
variable {G : Gauge} {m c f L : Side} {r s : ℕ}

private def grandR (u : Cross L (Loc G 1) (Loc G 1))(v : Cross L (Loc G 0) (Loc G 1)) : Cross L (Candles G) (Loc G 1) := fun i j x=> i.2.elim (fun k=> -v (i.1,k) j x) (fun k=> u (i.1,k) j x)
private lemma quarterbacks {u : Cross L (Loc G 1) (Loc G 1)}{v : Cross L (Loc G 0) (Loc G 1)} {σ A B : ℝ} (hp : u.strip σ A)(h : v.strip σ B) : (grandR u v).strip σ (max A B) := by
  intro i j; rcases i with ⟨i,x|x⟩
  · have he := strip_mono h le_rfl (le_max_right A B) (i,x) j; simpa [grandR,Width] using he
  exact strip_mono hp le_rfl (le_max_left A B) (i,x) j

def Speaks (u : Cross L (Loc G 1) (Loc G 1))(R : Cross L (Candles G) (Loc G 1))(Q : Cross L (Loc G 1) (Loc G 1)) : Prop := ∀ (c : Side)(p : Link G c),
    let s:Ratio c (c*L):=⟨L,rfl⟩
    let x:= installed s R*ᵥ p
    (bundleLink x)= installed s u*ᵥ p ∧ fderiv ℝ (dragged G (c*L)) 0 x=installed s Q *ᵥ p
private lemma meanspec (g : Lattice.Ratio c f) (Q : Cross g.count (Loc G 1) (Loc G 1)) (R : Cross g.count (Loc G 0) (Loc G 1)) (v : Link G c) :
    let x:= installed g (grandR Q R) *ᵥ v
    bundleLink x= installed g Q*ᵥ v ∧ siteMap ℝ x=-(installed g R*ᵥ v) := by
  intro x
  constructor
  · funext j; rfl
  funext i; change (installed g (grandR Q R)*ᵥ v) (i.1,.inl i.2)= - _
  unfold Matrix.mulVec dotProduct; rw [← Finset.sum_neg_distrib]; refine sum_congr rfl fun j _=>?_
  let k:=i.2
  have H : installed g (grandR Q R) (i.1,Sum.inl k) j = -installed g R i j := by
    unfold installed; simp only [submatrix_apply,split_co,id_eq,k]; unfold Row.acts; erw [Matrix.of_apply, Matrix.of_apply, ← tsum_neg]
    apply tsum_congr; intro z; dsimp only; split; rfl; exact (neg_zero ..).symm
  dsimp only; erw [H,neg_mul]

variable (G) (X : Chain) (N i : ℕ)
theorem ears (σ B : ℝ) (h : 0<σ) (P : Patch)(k : KernelChoices) (L : Repeated P.L) :
    ∃ C : ℝ,0≤C ∧ ∀ (u : Cross P.L (TypeFace 1) (TypeFace 1))(Q : Cross P.L (Loc G 1) (Loc G 1)), u.strip σ B →
        (∀ c (p : Link G c),
          let f:=c*P.L; let S:=linked P k c f rfl
          installed S.ratio Q *ᵥ p= patron G (extracted S (L.forest S.ratio) (installed S.ratio u)) *ᵥ p) →
          ∃ R : Cross P.L (Candles G) (Loc G 1), R.strip σ C ∧ Speaks (painted G u) R Q := by
  obtain ⟨K,hK,H⟩:= turn_fee G P L k σ h
  refine ⟨max 0 (max B (K*B)),le_max_left ..,fun u Q hv hp=>?_⟩
  obtain ⟨s,hs,he⟩:=H u B hv
  let A:= painted G u; let A':= grandR A s
  refine ⟨A',strip_mono (quarterbacks (paint_budget hv) hs) le_rfl (le_max_right ..),fun c p=>?_⟩
  let f:= c*P.L; let S:=linked P k c f rfl; let W:=installed S.ratio u; let T:=L.forest S.ratio
  change (bundleLink (installed S.ratio A' *ᵥ p)) = installed S.ratio A*ᵥ p ∧ _
  obtain ⟨hh,hy⟩:= meanspec S.ratio A s p; refine ⟨hh,?_⟩; rw [interpolate]
  have hx:= he c (c*P.L) rfl
  let J := patron G (straighten S T W)
  have hz : installed S.ratio s=J := by ext i j; rw [installed, submatrix_apply]; erw [hx]; change J ((unitSplit G S 0).symm (unitSplit G S 0 i)) j=_; rw [Equiv.symm_apply_apply]
  -- `BundleLink` definitional rest.
  change bundleLink (installed S.ratio (grandR A s)*ᵥ p)-gradientA G f (siteMap ℝ (installed S.ratio (grandR A s)*ᵥp))=_
  rw [hh,hy,hz,map_neg,sub_neg_eq_add,show installed S.ratio A=patron G W from paint_port ..]
  have ht:= hp c p; erw [ht]; unfold extracted; rw [patron_add,patron_mul,Matrix.add_mulVec,← Matrix.mulVec_mulVec]; rw [first_uniform,← patron_fee]

def fundsTor (G : Gauge) (σ B : ℝ) (P : Patch)(k : KernelChoices) (L : Repeated P.L) := if h:0<σ then (ears G σ B h P k L).choose else 1
lemma earn (h : X.Wake G) (hi : i<N) (g : KPrices X.kernel) :
    ∃ R : Cross (X.S.block i) (Candles G) (Loc G 1), R.strip (g.b (X.J i)) (fundsTor G (g.b (X.J i)) (g.bill (X.J i)) _ X.kernel (X.trees i)) ∧ Speaks (painted G (X.A₀ N i)) R (Chain.predict G X N i) := by
  have hp := g.positive (X.J i); let p:= X.patch i
  unfold fundsTor; rw [dif_pos hp]
  refine (ears G _ _ hp p X.kernel (X.trees i)).choose_spec.2 _ _ (strip_mono (az_strip X g N i [] (Nat.zero_le _)) le_rfl ?_) fun c v=>?_
  · simp only [List.length_nil,Nat.add_zero,pow_one]; exact div_le_self (g.solvent _) (by exact_mod_cast (X.S.block i).property)
  intro f S
  exact congr_arg (fun A=> A*ᵥ v) (Chain.predict_truth G h _ _ hi c f rfl) -- dot notation wrong implicit?

lemma poetic (F : Verse (Loc G 1)) (r : ℕ) (he : ∀ m,∃ f:Link G m→ℝ,Pointwise f∧ ∀ j≤ r,Tensor.coeff f j 0=recital (F j) m) (hv : ∀ i,Summable (F i))
    {A : Cross L (Loc G 1) (Loc G 1)} (hp : Whole A) {R : Cross L (Candles G) (Loc G 1)} (hs : Whole R)
    {Q : Cross L (Loc G 1) (Loc G 1)} (hQ : Whole Q) (h : Speaks A R Q):
    feather (F r) Q= feather (F r) A-∑ i ∈ range r,flow (cropWax (F i) r) R := by
  have ht U n (hU:Summable n) (hu:Whole (U:Cross L (Loc G 1) (Loc G 1))) : Tunable (feather (r:=r) n U) :=
    scroll_tune ((gem_tune n _ hU).1) (scan_whole hu)
  have hh i : Tunable (flow (cropWax (F i) r) R) := scroll_tune (grapes_summable L (silkSum (hv i))) hs
  refine (ht _ _ (hv _) hQ).unique ((ht _ _ (hv _) hp).sub (Tunable.sum _ (fun i _=> hh i))) fun m=>funext fun x=> ?_
  let f:=m*L; let s:Ratio m f:= ⟨L,rfl⟩; let a:= installed s R *ᵥ x
  obtain ⟨U,hS,H⟩:= he f
  have hx (Q' : Cross L (Loc G 1) (Loc G 1))(hq:Whole Q') : stanza (feather (F r) Q') m x= stanza (F r) f (installed s Q'*ᵥ x) := by
    rw [feather,scroll_play ((gem_tune _ _ (hv _)).1) (scan_whole hq)]; erw [scan_at s Q', gem_light (F r) (hv r) s, lodge_f]
  rw [stanza_sub ((ht _ _ (hv _) hp).1) ((Tunable.sum _ (fun i _=> hh i)).1), Pi.sub_apply, stanza_sum _ _ (fun i _=> (hh i).1),Finset.sum_apply, hx Q hQ, hx A hp]; 
  have ht' j : stanza (flow (cropWax (F j) r) R) m x= stanza (cropWax (F j) r) f a := flow_view (cropWax (F j) r) R (silkSum (hv j)) hs x
  simp_rw [ht'];
  obtain ⟨hV,hA⟩:= h m x; rw [← show _= installed s Q*ᵥ x from hA, ← show _= installed s A*ᵥ x from hV]; exact directed hS _ H hv
end YM.RG08.Staffer

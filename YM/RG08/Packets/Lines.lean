import YM.RG08.Packets.Mixed

/-!
# Substitution with changing plateaus and distinct field/curvature predictors

The factor `r*σ` at the *first* column is required (r is number of *other*
legs; held leg is not included in the arity parameter of `Packet`). Charge it before choosing L.
Moving to an earlier stage may require output width larger than input; old lengths here really do
rescale by 1/L, so charge it before block choice also.
-/
noncomputable section
namespace YM.RG08.Packets
open Filter Finset Pert.Bulk Laurent Lattice
open scoped Topology ENNReal

set_option autoImplicit false
variable {α β : Type} {r d : ℕ} {L : Side}
variable {K : Packet r α} {T B : Kernel α β} {U : Fin r→Kernel α β} {σ τ ω p q c : ℝ} {t : Fin r → ℝ} [Fintype α] [Fintype β]

def packetCoin (L : Side) (α β:Type) [Fintype α] [Fintype β] (d : ℕ) (q : ℝ) (t : Fin r → ℝ) :=
    ((Fintype.card α:ℝ)*(q*(L.val:ℝ)^4/(L.val:ℝ)^d)) * ∏ i, ((Fintype.card β:ℝ)*(t i/(L.val:ℝ)^d))

omit [Fintype α] in
theorem row_length (hω : σ ≤ ω) (hs : 0 ≤ σ) (hτ : σ ≤ L.val * τ)
    (h : Atlas ω L d B p) (x v : Market α) :
    ∑'z,bill (B v z) (σ*delta L x.1 z.1) ≤ ENNReal.ofReal (Fintype.card β * (p/(L.val:ℝ)^d)) * bill 1 (τ*sep x.1 v.1) := by
  rw [ENNReal.ofReal_mul (by positivity : 0≤ (Fintype.card β:ℝ)),ENNReal.ofReal_natCast,mul_assoc]
  apply convert_market
  intro i
  calc
    _ ≤ ∑' y:Cover,bill (B v (y,i)) (ω*delta L v.1 y + τ*sep x.1 v.1) := by
      apply ENNReal.tsum_le_tsum
      intro y
      apply bill_mono le_rfl
      have he : σ/L.val ≤ τ := by
        rw [div_le_iff₀ (by exact_mod_cast L.pos : (0:ℝ)<L.val)]
        linarith only [hτ]
      calc _ ≤ σ*(sep x.1 v.1 / L.val + delta L v.1 y) := mul_le_mul_of_nonneg_left (delta_fine ..) hs
           _ = (σ / L.val)*sep x.1 v.1 + σ * delta L v.1 y := by ring
           _ ≤ τ*sep x.1 v.1 + ω*delta L v.1 y := by
             exact add_le_add (mul_le_mul_of_nonneg_right he (sep_nonneg ..)) (mul_le_mul_of_nonneg_right hω (delta_nonneg ..))
           _ = _ := add_comm ..
    _ ≤ _ := by
      simp_rw [bill_add,ENNReal.tsum_mul_right,show bill 1 (τ*sep x.1 v.1) = ENNReal.ofReal (Real.exp (τ*sep x.1 v.1)) by simp [bill]]
      gcongr
      exact h.row ..

theorem mixed_lines (hT : Atlas ω L d T q) (h : ∀ i,Atlas ω L d (U i) (t i))
    (hK : Folded τ K p) (hs : 0 ≤ σ) (hw : σ ≤ ω) (hr : r * σ ≤ ω) (hτ : σ ≤ L.val * τ) :
    Folded σ (push K T (fun i _=> U i)) (packetCoin L α β d q t*p) ∧
      ∀ z y, Summable fun a : Market α × (Fin r→Market α)=> term K T (fun i _=> U i) z y a.1 a.2 := by
  have hv := hT.nonneg
  let A (i : Fin r) := (Fintype.card β:ℝ)*(t i/(L.val:ℝ)^d)
  let C := (Fintype.card α:ℝ)*(q*(L.val:ℝ)^4/(L.val:ℝ)^d)
  have hU : purse (fun i _=> U i) L σ τ (fun i=> ENNReal.ofReal (A i)) := fun i => row_length hw hs hτ (h i)
  exact ⟨push_est K T _ L A C p hU hK hs (use_head hr hT) (by unfold C; positivity) (fun i=>by have ht := (h i).nonneg; unfold A; positivity),fun z y=> pushes K T _ L A C p hU hK hs (use_head hr hT) y z⟩

omit [Fintype α] in
theorem row_save (hs : 0 < τ) (hσ : 0 ≤ σ) (hω : σ ≤ ω) (hτ : 2*σ ≤ L.val * τ)
    (h : Atlas ω L d B q) (x v : Market α) :
    ∑'z,bill (centered B x v z) (σ*delta L x.1 z.1) ≤
      ENNReal.ofReal (Fintype.card β * ((2/τ)*q/(L.val:ℝ)^(d+1))) * bill 1 (τ*sep x.1 v.1) := by
  rw [ENNReal.ofReal_mul (by positivity : 0≤ (Fintype.card β:ℝ)),ENNReal.ofReal_natCast,mul_assoc]
  apply convert_market
  intro i
  let a := sep x.1 v.1
  have ha : 0 ≤ a := sep_nonneg ..
  have hL : 0 < (L.val:ℝ) := by exact_mod_cast L.pos
  have hPrice : a * Real.exp (σ*(a/L.val)) ≤ (2/τ)*Real.exp (τ*a) := by
    calc _ ≤ ((2/τ)*Real.exp (τ*a/2))*Real.exp (τ*a/2) := by
           gcongr
           · rw [div_mul_eq_mul_div, le_div_iff₀ hs]; linarith only [Real.add_one_le_exp (τ*a/2)]
           · rw [← mul_div_assoc, div_le_iff₀ hL]; nlinarith only [mul_le_mul_of_nonneg_right hτ ha]
         _ = _ := by rw [mul_assoc,← Real.exp_add,show τ*a/2+τ*a/2=τ*a by ring]
  have hq := h.nonneg
  calc
    _ ≤ ENNReal.ofReal (Laurent.size _ *diffScale _ d σ _ _ _) := atlas_difference (h.mono hω hσ) v.2 i x.1 v.1
    _ ≤ _ := by
      rw [bill,abs_one,one_mul,← ENNReal.ofReal_mul (by positivity : 0≤ (2 / τ) * q/(L.val:ℝ)^(d+1))]
      apply ENNReal.ofReal_le_ofReal
      rw [diffScale, ← mul_assoc, sep_comm v.1 x.1,show ((Laurent.size (v.1-x.1)):ℝ)=a from (sep_comm v.1 x.1)]
      exact (mul_le_mul_of_nonneg_right hPrice (div_nonneg hq (pow_nonneg hL.le _))).trans_eq (by unfold a; ring)

def neutralCoin (L : Side) (α β:Type) [Fintype α] [Fintype β] (τ q t : ℝ) :=
    (Fintype.card α:ℝ)*q*(Fintype.card β*(2/τ)*t)/(L.val:ℝ)

theorem push_null {K : Packet 1 α} (hT : Atlas ω L 2 T q) (hU : Atlas ω L 2 B c)
    (hK : Folded τ K p) (ht : 0 < τ) (hs : 0 ≤ σ) (hw : σ ≤ ω) (hτ : 2*σ ≤ L.val * τ) (h₀:neutral K) :
    Folded σ (push K T (fun _ _=> B)) (neutralCoin L α β τ q c*p) := by
  have hv (x) := bill_folded x ht.le hK
  have he x y (w : Market α→Market α) : Summable fun z=> K x (fun _=>z)*B (w z) y := by
    apply Summable.of_norm_bounded ((hv x).norm.mul_right c); intro z; rw [_root_.norm_mul]; exact mul_le_mul_of_nonneg_left (atlas_entry hU ..) (norm_nonneg _)
  have hId : push K T (fun _ _=> B) = push K T (fun _=> centered B) := by
    funext y z
    unfold push
    refine tsum_congr fun x=> congr_arg (T x y * ·) ?_
    rw [transmit_one K (fun _=>B),transmit_one K (centered B)]
    simp_rw [centered,mul_sub] ; rw [Summable.tsum_sub (he x (z 0) (fun w=>w)) (he x (z 0) (fun w=>(x.1,w.2)))] -- definally id?
    let f (u:Cover)(i:α) := K x (fun _=> (u,i)) * B (x.1,i) (z 0)
    have hq' := (Equiv.prodComm α Cover).tsum_eq (f:=fun w=>f w.fst w.snd)
    have hy' (i:α) : ∑' u,f u i=0 := by unfold f; rw [tsum_mul_right,h₀,zero_mul]
    have hs' : ∑' w:α × Cover,f w.2 w.1=∑' i:α,∑' u:Cover,f u i := (he x (z 0) (fun w=>(x.1,w.2))).prod_symm.tsum_prod
    have hZero : ∑'w:Market α, K x (fun _=>w)*B (x.1,w.2) (z 0)=0 := hq'.symm.trans (hs'.trans (by simp_rw [hy',tsum_zero]))
    rw [hZero,sub_zero]
  rw [hId]
  let A := Fintype.card β * ((2/τ)*c/(L.val:ℝ)^3)
  let D := Fintype.card α * q * (L.val:ℝ)^2
  have hP : purse (fun _ : Fin 1=> centered B) L σ τ (fun _=> ENNReal.ofReal A) := fun _=>row_save ht hs hw hτ hU
  have hq := hT.nonneg; have hv' := hU.nonneg
  convert push_est K T (fun _=>centered B) L (fun _=>A) D p hP hK hs (by simpa [D] using use_head2 (L:=L) hw hT) (by unfold D; positivity) (fun _=>by unfold A; positivity) using 1
  simp only [Fin.prod_univ_succ,Fintype.prod_empty, mul_one]
  unfold A D neutralCoin
  field_simp

end YM.RG08.Packets

import YM.RG08.Packets.Lines

/-!
# Real algebra across the first-root transmission

Summability for reindexing the two-level/join sums. Check *neutrality* (zero affine value in
each type, not just kinetic trace) after the quadratic transfer. No Ward assumptions used here,
as long as supplies give the constant-curvature travels property separately (uses of Bianchi
or symmetry are later).
-/
noncomputable section
namespace YM.RG08.Packets
open Filter Finset Pert.Bulk Laurent Lattice Function
open scoped Topology ENNReal

set_option autoImplicit false
variable {α β : Type} {r d : ℕ} {L : Side}
variable {K B : Packet r α} {T : Kernel α β} {U : Fin r→Kernel α β} {σ τ ω p q p' : ℝ} {t : Fin r → ℝ} [Fintype α] [Fintype β]

theorem sails (hT : Atlas ω L d T q) (h : ∀ i,Atlas ω L d (U i) (t i))
    (hK : Folded τ K p) (y) (hτ : 0 ≤ τ) :
    Summable (fun j : (Fin r→Market β) × (Market α × (Fin r→Market α)) => term K T (fun i _=> U i) j.1 y j.2.1 j.2.2) := by
  let A (i : Fin r) := (Fintype.card β:ℝ)*(t i/(L.val:ℝ)^d)
  let C := (Fintype.card α:ℝ)*(q*(L.val:ℝ)^4/(L.val:ℝ)^d)
  have hω := hT.width
  have hU : purse (fun i _=> U i) L 0 τ (fun i=> ENNReal.ofReal (A i)) := fun i=> row_length hω le_rfl (mul_nonneg (by positivity) hτ) (h i)
  have hv (s : Finset (Fin r)) : (∏ i ∈ s, ENNReal.ofReal (A i)) ≠ ⊤ := by
    induction s using Finset.induction_on with
    | empty => simp
    | insert a s ha ih => rw [prod_insert ha]; exact ENNReal.mul_ne_top (by simp) ih
  apply summable_from_receipt (fun _=>le_refl 0)
  rw [ENNReal.tsum_prod (f:=fun z (a : Market α × (Fin r→Market α))=> bill (term K T (fun i _=> U i) z y a.1 a.2) 0)]
  apply ne_top_of_le_ne_top (b:=ENNReal.ofReal C*(∏ i, ENNReal.ofReal (A i))*ENNReal.ofReal p) (ENNReal.mul_ne_top (ENNReal.mul_ne_top (by simp) (hv _)) (by simp))
  simpa only [charge,zero_mul] using revenue K T (fun i _=> U i) L (fun i=>ENNReal.ofReal (A i)) (ENNReal.ofReal C) (ENNReal.ofReal p) hU hK le_rfl (use_head (by simpa using hω) hT) y

theorem plus_sail (hT : Atlas ω L d T q) (h : ∀ i,Atlas ω L d (U i) (t i))
    (hK : Folded τ K p) (hB : Folded τ B p') (hτ : 0 ≤ τ) :
    push (fun x w=> K x w+B x w) T (fun i _=>U i)=fun x w=>push K T (fun i _=>U i) x w+push B T (fun i _=>U i) x w := by
  funext y z
  let f (K : Packet r α) (a:Market α × (Fin r→Market α)) := term K T (fun i _=> U i) z y a.1 a.2
  have hSK := (mixed_lines hT h hK (le_refl 0) hT.width (by simpa using hT.width) (mul_nonneg (by positivity) hτ)).2 z y
  have hSB := (mixed_lines hT h hB (le_refl 0) hT.width (by simpa using hT.width) (mul_nonneg (by positivity) hτ)).2 z y
  have hs : f (fun x w=> K x w+B x w) = f K + f B := funext fun i=> by dsimp [f,term]; ring
  have hSP : Summable (f (fun x w=> K x w+B x w)) := hs ▸ hSK.add hSB
  exact (push_full _ _ _ _ _ hSP).trans (by
    rw [push_full _ _ _ _ _ hSB,push_full _ _ _ _ _ hSK,← hSK.tsum_add hSB]
    exact tsum_congr (congr_fun hs))

omit [Fintype α] [Fintype β] in
theorem c_sail (c : ℝ) :
    push (fun x w=> c*K x w) T (fun i _=>U i) = fun x w=> c*push K T (fun i _=>U i) x w := by
  funext y z
  simp only [push]
  simp_rw [mul_assoc c (K _ _), tsum_mul_left,mul_left_comm (T _ _) c,tsum_mul_left]

theorem minus_sail (hT : Atlas ω L d T q) (h : ∀ i,Atlas ω L d (U i) (t i))
    (hK : Folded τ K p) (hB : Folded τ B p') (hτ : 0 ≤ τ) :
    push (fun x w=> K x w-B x w) T (fun i _=>U i)=fun x w=>push K T (fun i _=>U i) x w-push B T (fun i _=>U i) x w := by
  have he : Folded τ (fun x w=> -B x w) p' := (ticket_folded ..).1 (((ticket_folded ..).2 hB).neg)
  simp_rw [sub_eq_add_neg, plus_sail hT h hK he hτ,← neg_one_mul (B _ _),c_sail,neg_one_mul]

theorem ships {K : Packet 1 α} {B : Kernel α β} (hT : Atlas ω L d T q) (hB : Atlas ω L d B p')
    (hK : Folded τ K p) (hτ : 0 ≤ τ) (y) :
    Summable (fun j : Market β × (Market α × Market α) => T j.2.1 y * K j.2.1 (fun _=>j.2.2) * B j.2.2 j.1) := by
  let e : ((Fin 1 → Market β) × (Market α × (Fin 1 → Market α))) ≃ Market β × (Market α × Market α) :=
    (identify _).prodCongr ((Equiv.refl _).prodCongr (identify _))
  apply e.summable_iff.mp
  convert sails (r:=1) hT (fun _=>hB) hK y hτ using 1
  funext j
  have hw : j.2.2 = fun _ : Fin 1=> j.2.2 0 := funext fun i=> by rw [Fin.fin_one_eq_zero i]
  change (T j.2.1 y * K j.2.1 (fun _=> j.2.2 0) * B (j.2.2 0) (j.1 0)) = _
  conv_lhs => rw [← hw]
  rw [term,Fin.prod_univ_succ]; simp

def travels (B : Kernel α β) : Prop := ∀ (i j), ∃ t : ℝ, ∀ x:Cover, ∑'y, B (x,i) (y,j) = t

theorem invariant {K : Packet 1 α} {B : Kernel α β} (hT : Atlas ω L d T q) (hB : Atlas ω L d B p')
    (hK : Folded τ K p) (hτ : 0 ≤ τ) (h₀:neutral K) (hu: travels B) :
    neutral (push K T (fun _ _=>B)) := by
  intro y i
  let e (z : Cover) (a : Market α × Market α):= T a.1 y * K a.1 (fun _=>a.2) * B a.2 (z,i)
  have hMap : Injective (Prod.map (fun z:Cover=> ((z,i):Market β)) (fun a : Market α × Market α => a)) := by intro a b ab; simpa only [Prod.map,Prod.mk.injEq,eq_self,and_true,Prod.ext_iff] using ab
  have hs := (ships hT hB hK hτ y).comp_injective hMap
  change Summable (fun k : Cover × (Market α × Market α)=> e k.1 k.2) at hs
  have hh z : push K T (fun _ _=>B) y (fun _=>(z,i)) = ∑' a,e z a := by
    unfold push
    simp_rw [transmit_one K (fun _=>B)]
    rw [(hs.prod_factor z).tsum_prod]
    unfold e
    simp_rw [mul_assoc,tsum_mul_left]
  have hi (x:Market α) (i':α) :
      ∑' w:Cover, (∑' z,e z (x,(w,i')))=0 := by
    obtain ⟨s,hf⟩:=hu i' i
    unfold e
    simp only [tsum_mul_left, tsum_mul_right, hf, h₀ x i', mul_zero, zero_mul]
  have hv (x:Market α) :
      ∑' w:Market α, (∑' z,e z (x,w))=0 := by
    let f (w:Cover)(i':α):= ∑' z,e z (x,(w,i'))
    have hq' := (Equiv.prodComm α Cover).tsum_eq (f:=fun w=>f w.fst w.snd)
    have hb : Summable (fun a : Market α × Market α=>∑' z,e z a) := hs.prod_symm.prod
    have ht : ∑' w:α×Cover, f w.2 w.1=∑' i':α,∑' u:Cover,f u i' := (hb.prod_factor x).prod_symm.tsum_prod
    exact hq'.symm.trans (ht.trans ((tsum_congr (hi x)).trans tsum_zero))
  simp_rw [hh]
  rw [hs.prod_symm.tsum_comm]; exact hs.prod_symm.prod.tsum_prod.trans <| (tsum_congr hv).trans tsum_zero

end YM.RG08.Packets

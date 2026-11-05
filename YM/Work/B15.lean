import YM.Bid.Fetch

/-!
# B15 – full translated cutoff trains under a centered Episode budget
-/
set_option autoImplicit false
noncomputable section

namespace YM.Work.B15

open Set Filter Function MeasureTheory Lattice Cells Wilson Extraction Spec Bid
open scoped BigOperators

variable {G : Gauge} {C : Family G} {n : Side}

lemma rootTest_star (T : Tiling n) (β : ℝ) (Z : Config G n → ℂ) :
    T.rootTest β (fun u => star (Z u)) = T.rootTest β Z := by
  have hcopy (v u) : T.copy v (fun x => star (Z x)) u = star (T.copy v Z u) := by
    unfold Tiling.copy; split <;> rfl
  unfold Tiling.rootTest
  simp_rw [hcopy, ← star_prod]
  rw [show moment β (fun U => star (∏ i, T.copy i Z U)) = star (moment β (fun U => ∏ i, T.copy i Z U)) from
    by simp only [moment, Complex.star_def, integral_conj], norm_star]

/-- Even-cell addresses (same scalar shift along every coordinate). -/
def diag (t j : ℕ) : Cover := fun _ => ↑(2*t*j)

def addr (T : Tiling n) (t j : ℕ) : T.Cell := wrap T.period (diag t j)

lemma addr_apply (T : Tiling n) (t j : ℕ) (a : Axis) : addr T t j a = ↑(2*t*j) := by
  change ((↑(2*t*j) : ℤ) : Per T.period) = ↑(2*t*j)
  exact Int.cast_natCast _

lemma addr_even (T : Tiling n) (t j : ℕ) : T.omega (addr T t j) = 1 := by
  refine Signed.ext rfl ?_
  ext i
  change decide (T.parity (addr T t j i) ≠ 0) = false
  simp only [addr_apply, Tiling.parity,map_natCast]
  simp [show (2 : ZMod 2)=0 from rfl]

lemma addr_copy (T : Tiling n) (t j : ℕ) (Z : Config G n → ℂ) (U : Config G n) :
    T.copy (addr T t j) Z U = Z (translate (T.units.root (addr T t j)) U) := by
  have he : ¬ T.hand (addr T t j) := by
    simp [Tiling.hand,addr_even,Finset.filter_false_of_mem]
  have hb : T.bias (addr T t j)=0 := by ext1 i; simp [Tiling.bias,addr_even]
  have hd : T.translateBy (addr T t j) = T.units.root (addr T t j) := by
    rw [Tiling.translateBy, hb, addr_even, Signed.act_one, Tiling.starts, add_sub_cancel_left,add_zero]
  rw [Tiling.copy,if_neg he,hd,addr_even,pull_one]

lemma addr_inj (T : Tiling n) {t l : ℕ} (ht : 0<t) (hsize : 2*t*l ≤ T.period.val) :
    Injective (fun j : Fin l => addr T t j.val) := by
  have hpos : 0 < 2*t := by omega
  have hlt (j : Fin l) : 2*t*j.val < T.period.val := (Nat.mul_lt_mul_of_pos_left j.isLt hpos).trans_le hsize
  intro x y h
  have hd := congr_arg (fun z : T.Cell => (z 0).val) h
  change (addr T t x.val 0).val = (addr T t y.val 0).val at hd
  rw [addr_apply,addr_apply,ZMod.val_natCast_of_lt (hlt x),ZMod.val_natCast_of_lt (hlt y)] at hd
  exact Fin.ext (Nat.eq_of_mul_eq_mul_left hpos hd)

lemma count_trans {b k : Side} (g : Ratio k n) (h : Ratio b k) (z : Ratio b n) :
    z.count.val = g.count.val * h.count.val := by
  apply Nat.eq_of_mul_eq_mul_left b.property
  calc b.val * z.count.val = n.val := z.exact_size.symm
       _ = k.val * g.count.val := g.exact_size
       _ = b.val * h.count.val * g.count.val := congr_arg (fun q : ℕ => q * g.count.val) h.exact_size
       _ = b.val * (g.count.val * h.count.val) := by ac_rfl

lemma addr_root {k N b : ℕ} (C : Family G) (e : b ≤ k) (hN : k ≤ N) (p t j : ℕ) :
    let T := center C.S p (e.trans hN) 0
    T.units.root (addr T t j) = location C.S k N p (Episode.step C e t j) := by
  intro T
  have he : Episode.step C e t j = (C.S.toDepth e p).count.val • diag t j := by
    funext i
    change ((↑((C.S.toDepth e p).count.val*(2*t*j)) : ℤ)) = _
    simp only [Nat.cast_mul,Pi.smul_apply,nsmul_eq_mul,diag]
  have hx := count_trans (C.S.toDepth hN p) (C.S.toDepth e p) T.units
  rw [location,dif_pos hN, he, addr,Ratio.root_embed, Ratio.embed_wrap, Ratio.embed_wrap, smul_smul, ← hx]

variable {F : Extraction.Order} {k : ℕ}

lemma cuts_translate (E : Episode C F k) (N p : ℕ) (q : Cover) (U : Config G (C.side N p)) :
    E.cuts N p 0 (translate (location C.S k N p q) U) = E.cuts N p q U := by
  simp_rw [Episode.cuts,add_zero,C.translation,Order.location_add]

lemma cutoff_bound {b N p : ℕ} (e : b ≤ k) (hk : k ≤ N) (E : Episode C F k) (m t : ℕ) (ht : 0<t)
    (H : Seam G (C.side N p) (C.beta N p)) (hsize : 2*t*(2*m) ≤ (C.side b p).val) {c : ℝ}
    (hx : Interior ((center C.S p (e.trans hk) 0).chamber 0) (E.cuts N p 0))
    (hc : (center C.S p (e.trans hk) 0).rootTest (C.beta N p) (E.cuts N p 0) ≤ c) :
    ‖E.fromCut e t m N p‖ ≤ c ^ (2*m) := by
  let T := center C.S p (e.trans hk) 0
  let v (j : Fin (2*m)) : Config G (C.side N p) → ℂ := if j.val%2=0 then fun U => star (E.cuts N p 0 U) else E.cuts N p 0
  have hI (j) : Interior (T.chamber 0) (v j) := by dsimp only [v]; split; exact hx.real; exact hx
  have hV (j) : T.rootTest (C.beta N p) (v j) ≤ c := by
    dsimp only [v]; split
    · rw [rootTest_star]; exact hc
    exact hc
  have he : E.twice e t m N p = (fun U => ∏ j, T.copy (addr T t j.val) (v j) U) := by
    funext U
    unfold Episode.twice
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [addr_copy,addr_root C e hk]
    dsimp only [v]; split <;> simp only [cuts_translate]
  calc ‖E.fromCut e t m N p‖ = ‖moment (C.beta N p) (fun U => ∏ j, T.copy (addr T t j.val) (v j) U)‖ := by rw [Episode.fromCut,he]
       _ ≤ ∏ j, T.rootTest (C.beta N p) (v j) := T.planted H _ (addr_inj T ht hsize) _ hI
       _ ≤ ∏ _j : Fin (2*m), c := Finset.prod_le_prod (fun _ _ => T.root_nonneg _ _) (fun j _ => hV j)
       _ = c ^ (2*m) := by simp

theorem answer : Bid.B15 := by
  intro G C F S s k b e E g _ hs t ht n ε hε
  have h := hs ε hε
  unfold Order.late at h ⊢
  have hp : ∀ᶠ l in atTop, 2*t*(2*n) ≤ (C.S.period (F.per l)).val :=
    (C.S.period_strict.tendsto_atTop.comp F.per.cofinal).eventually (eventually_ge_atTop (2*t*(2*n)))
  filter_upwards [h,hp] with l hl hsize
  have hd : 2*t*(2*n) ≤ (C.side b (F.per l)).val := hsize.trans (Nat.le_mul_of_pos_right _ (C.S.denominator b).property)
  filter_upwards [hl,F.mesh.cofinal.eventually (eventually_ge_atTop k)] with i hi hk
  obtain ⟨hb,hx,hc⟩ := hi
  exact cutoff_bound e hk E n t ht (s.copies.all _ _) hd hx hc

-- Edge checks: empty train; an early (too small relative to t) period need not work.
example {b : ℕ} (e : b ≤ k) (E : Episode C F k) (t N p : ℕ) : E.fromCut e t 0 N p = 1 := by
  simp [Episode.fromCut,Episode.twice,moment]

example (T : Tiling n) : ¬ Injective (fun j : Fin 2 => addr T T.period.val j.val) := by
  intro h
  apply (show (0:Fin 2) ≠ 1 by decide)
  apply h
  funext i
  simp [addr_apply, Per]

end YM.Work.B15

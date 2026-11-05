import YM.Slice.Calendar

/-! Cyclic gap arithmetic. Put moving point first; at least two on circle. -/
set_option autoImplicit false
noncomputable section
namespace YM.Slice.Time
open Function Set MeasureTheory Lattice Wilson
open scoped Topology BigOperators Matrix.Norms.Frobenius
variable {a : Axis} {G : Gauge} {m : ℕ} {n : Side}

lemma success {B : Fin (m+1) → Brick a G n} {Y : Fin (m+1) → ℕ} {b : Fin (m+1) → Per n}
    (h : ∀ i : Fin m, b i.succ = b i.castSucc + (B i.castSucc).width + Y i.castSucc)
    (U : Config G n) : Time.word (drive B Y) (b 0) U = ∏ i, (B i).value (b i) U := by
  induction m with
  | zero =>
    rw [welded,distributed]
    simp only [Time.read,crossing,mul_one]; simp [drive]
  | succ k ih =>
    rw [welded,Time.distributed,Time.read,crossing,mul_one]
    have hp (i : Fin k) : Fin.tail b i.succ = Fin.tail b i.castSucc + (Fin.tail B i.castSucc).width + Fin.tail Y i.castSucc := h i.succ
    have ht : b 0 + ((B 0).width : Per n) + (Y 0:Per n) = Fin.tail b 0 := (h 0).symm
    rw [starts,duration_temp,Nat.cast_add, ← add_assoc,ht,ih hp]
    conv_rhs => rw [Fin.prod_univ_succ]
    rfl

/-- Arithmetic natural distances on sorted circle. -/
def minutes (x : Fin (m+1)→Per n) (i : Fin (m+1)) := (x i-x 0).val

def sectionGap (x : Fin (m+1) → Per n) (i : Fin m) := minutes x i.succ - minutes x i.castSucc
def finalGap (x : Fin (m+1)→ Per n) := n.val - minutes x (Fin.last m)

def cyclicGaps (x : Fin (m+1)→ Per n) := (Fin.snoc (α := fun _ => ℕ) (sectionGap x) (finalGap x))

lemma section_rel {x : Fin (m+1) → Per n} (h : StrictMono (minutes x)) (i : Fin m) :
    minutes x i.succ = minutes x i.castSucc + sectionGap x i := by
  have he : i.castSucc < i.succ := Fin.castSucc_lt_succ
  have hh := h he; unfold sectionGap; omega

lemma section_duration {x : Fin (m+1) → Per n} (h : StrictMono (minutes x)) (i : Fin m) :
    sectionGap x i=(x i.succ - x i.castSucc).val := by
  have hx : sectionGap x i<n.val := by
    have hp : minutes x i.succ<n.val := ZMod.val_lt _
    rw [section_rel h i] at hp; omega
  rw [← ZMod.val_natCast_of_lt hx]
  apply congr_arg ZMod.val
  rw [sectionGap,Nat.cast_sub (h.monotone (Fin.castSucc_lt_succ).le)]; unfold minutes; simp

lemma sum_time {x : Fin (m+1)→ Per n} (h : StrictMono (minutes x)) : ∑ i, cyclicGaps x i = n.val := by
  let f := minutes x
  have ht : f 0=0 := by simp [f,minutes]
  have he (i : Fin m) : f i.succ=f i.castSucc+cyclicGaps x i.castSucc := by rw [cyclicGaps, Fin.snoc_castSucc]; exact section_rel h i
  have hy : (∑ i : Fin m, f i.succ)+f 0=(∑ i : Fin m, f i.castSucc)+f (Fin.last _) := by
    rw [← Fin.sum_univ_castSucc, Fin.sum_univ_succ];ring
  have hx : ∑ i : Fin m, cyclicGaps x i.castSucc=f (Fin.last m) := by
    simp only [he,Finset.sum_add_distrib,ht, add_zero] at hy; omega
  rw [Fin.sum_univ_castSucc,hx,cyclicGaps,Fin.snoc_last]; unfold finalGap
  exact Nat.add_sub_of_le (show f _≤ n.val from (ZMod.val_lt _).le)

lemma last_val {x : Fin (m+1) → Per n} (h : StrictMono (minutes x)) (hm : 0 < m) : finalGap x=(x 0 - x (Fin.last m)).val := by
  have he : 0<minutes x (Fin.last m) := by
    have hs : 0 < Fin.last m := by simpa [Fin.lt_def]
    simpa [minutes] using (h hs)
  have hx := show minutes x (Fin.last m)<n.val from ZMod.val_lt _
  have hv : finalGap x<n.val := by unfold finalGap; omega
  rw [← ZMod.val_natCast_of_lt hv]; apply congr_arg ZMod.val
  rw [finalGap,Nat.cast_sub hx.le]; unfold minutes; simp [Per]

lemma organized {x : Fin (m+1)→ Per n} {B : Fin (m+1)→Brick a G n} (w : ℕ) (hB : ∀ i, (B i).width=w)
    (p : ℕ) (hp : 0<p) (hn : n.val=(p+p)*w) (D : StrictMono (minutes x))
    (r : ℝ) (hr : 0<r) (N : 0<m)
    (he : ∀ i j, i ≠ j → (w:ℝ)+2*r < (x j-x i).val)
    (β) (hβ : 0 ≤ β) {l : ℕ} (hL : (l:ℝ) ≤ r) {K : Fin (m+1)→ℝ}
    (hK : ∀ i, ‖moment β (Time.word (column (B i) p) (x i))‖^(Holder.rate p) ≤ K i) :
    let X (i : Fin (m+1)) := if i=0 then x i + ↑l else x i
    ‖moment β (fun U => ∏ i, (B i).value (X i) U) - moment β (fun U => ∏ i, (B i).value (x i) U)‖ ≤
      (∏ i, K i)/r*(l:ℝ) := by
  intro X
  let Y := fun i => cyclicGaps x i - w
  have hh (i) : (w:ℝ)+2*r < cyclicGaps x i := by
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [cyclicGaps,Fin.snoc_last,last_val D N]; exact he _ _ (ne_of_gt (by simpa [Fin.lt_def]))
    rw [cyclicGaps, Fin.snoc_castSucc, section_duration D]; exact he _ _ (Fin.castSucc_lt_succ).ne
  have hw (i) : w + Y i = cyclicGaps x i := by
    apply Nat.add_sub_of_le; apply Nat.le_of_lt; exact Nat.cast_lt.mp (lt_trans (by linarith) (hh i))
  have hv (i) : 2*r < Y i := by have hh := hh i; rw [← hw,Nat.cast_add] at hh;linarith
  let j := Fin.last m
  let Z (i : Fin (m+1)) := if i=j then Y j + l else if i=0 then Y 0-l else Y i
  have hj : j≠0 := ne_of_gt (by unfold j;simpa [Fin.lt_def])
  have hO : (l:ℝ)<Y 0 := lt_trans (by linarith) (hv 0)
  have hx0 : Z 0+l=Y 0 := by rw [show Z 0=Y 0-l by simp [Z,hj.symm]]; exact Nat.sub_add_cancel (Nat.cast_lt.mp hO).le
  have hxj : Z j=Y j+l := by simp [Z]
  have hx (a : Fin (m+1)) (h : a≠j) (he : a≠0) : Z a=Y a := by simp [Z,h,he]
  have hY : (m+1)*w+∑ i, Y i=n.val := by
    rw [← sum_time D,show cyclicGaps x = fun i => w+Y i from funext fun i => (hw i).symm] -- rhs Y unfolds?
    simp [Finset.sum_add_distrib]
  have hZ : (m+1)*w+∑ i, Z i=n.val := by
    suffices e : ∑ i, Z i=∑ i, Y i by rw [e,hY]
    have he i : Z i + (if i=0 then l else 0)=Y i+(if i=j then l else 0) := by
      by_cases h:i=0
      · subst i; rw [if_pos rfl,if_neg hj.symm,hx0];simp
      by_cases e:i=j
      · subst i; simp [h,hxj]
      simp [h,e,hx]
    have hv := Finset.sum_congr (rfl : Finset.univ = _) fun i _ => he i
    simpa [Finset.sum_add_distrib] using hv
  have hf (i : Fin m) : x i.succ=x i.castSucc + ↑(B i.castSucc).width+(Y i.castSucc:Per n) := by
    rw [hB,add_assoc,← Nat.cast_add,hw,cyclicGaps, Fin.snoc_castSucc,section_duration D];simp [Per]
  have hF (i : Fin m) : X i.succ=X i.castSucc + ↑(B i.castSucc).width+(Z i.castSucc:Per n) := by
    rw [show X i.succ=x i.succ by simp [X],hf]
    by_cases H:i.castSucc=0
    · rw [H,← hx0,show X 0=x 0+l by simp [X],Nat.cast_add]; ring
    rw [hx i.castSucc (show i.castSucc≠j from (Fin.castSucc_lt_last i).ne) H, show X i.castSucc=x i.castSucc by simp [X,H]]
  have hg : 0<w := hB 0 ▸ (B 0).width_pos
  simp_rw [← success hF, ← success hf]
  exact Time.powering β hβ B hn hp hg hB hY hZ j 0 hj hxj.symm hx0 (fun i hi h => (hx i hi h).symm) r hr hv hL (X 0) (x 0) _ K hK
end YM.Slice.Time

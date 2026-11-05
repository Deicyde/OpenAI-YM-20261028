import YM.Next.UV_STRESS.Influence
import YM.Work.B15

/-!
# Backward expectations down the actual history, for rooted probes

Including pullback of products of centered copies. This is where disjointness
matters. One site tag per coarse site (uses `back_packs`). No such product rule
asserted just from a normalized kernel. Keep actual β of THIS cutoff N at each
step; padding of curves outside the k:N zone irrelevant.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Set Function Filter MeasureTheory Analysis Lattice Wilson RG Cells
open scoped Topology BigOperators
variable {G : Gauge} (C : Family G)

abbrev operation (p m : ℕ) := C.path.levels.clock.op m p
lemma step_approved (p m : ℕ) : (operation C p m).patch.Branches (operation C p m).kernel G :=
    (C.path.levels.blocks m p).branches

/-- m ≥ k, no fake output history when m below k. -/
def stack (p N k m : ℕ) (F : Config G (C.side k p) → ℂ) (h : k ≤ m) : Config G (C.side m p) → ℂ :=
  if e : m=k then (by subst m; exact F) else
    match m with
    | 0 => by omega
    | m+1 => back (operation C p m) (C.path.β N p (m+1)) (stack p N k m F (by omega))
termination_by m

variable (p N k m : ℕ) (F : Config G (C.side k p) → ℂ)

lemma stack_origin (h : k≤k) : stack C p N k k F h=F := by
  rw [stack]; simp
lemma stack_step (h : k ≤ m) : stack C p N k (m+1) F (h.trans (Nat.le_succ _))=
    back (operation C p m) (C.path.β N p (m+1)) (stack C p N k m F h) := by
  rw [stack,dif_neg (by omega)]

lemma stack_envelope (h : k ≤ m) (hp : Envelope F) : Envelope (stack C p N k m F h) := by
  induction m,h using Nat.le_induction with
  | base => rw [stack_origin]; exact hp
  | succ m h ih => rw [stack_step C p _ k m _ h]; exact pulled _ ih (step_approved ..) _
lemma stack_bound (h : k ≤ m) (A : ℝ) (hp : ∀ V, ‖F V‖ ≤ A) : ∀ x, ‖stack C p N k m F h x‖ ≤ A := by
  induction m,h using Nat.le_induction with
  | base => rw [stack_origin]; exact hp
  | succ m h ih => rw [stack_step C p _ k m _ h]; exact keeps_bound _ (step_approved ..) _ _ ih

lemma stack_region (h : k ≤ m) (r : ℕ) (hp : Interior (region (C.side k p) r) F) :
    Interior (region (C.side m p) (advanceSize C k r m)) (stack C p N k m F h) := by
  induction m,h using Nat.le_induction with
  | base => rw [stack_origin,first_radius]; exact hp
  | succ m h ih => rw [stack_step C p N k m F h,next_radius C r p k m h]; exact
      (through (operation C p m) (step_approved ..) (C.path.β N p (m+1)) ih).enlarges (travel_shadow _ _)

-- maps needed for copies and expectation

lemma copy_step (p m : ℕ) {t : ℕ} (hm : t≤m) (i : Site (C.side t p)) :
    let Q := center C.S p hm 0
    let M := center C.S p (hm.trans (Nat.le_succ m)) 0
    M.translateBy i = (operation C p m).ratio.embed (Q.translateBy i) := by
  intro Q M
  have he (m : ℕ) (h : t≤m) : (center C.S p h 0).translateBy i=(C.S.toDepth h p).embed i := by
    have he := copy_home C.S h 0 i; rwa [Tiling.copyMap,affine, Signed.act_zero, zero_add, zero_add] at he
  dsimp only [Q,M]; rw [he,he]
  let S := C.S.toDepth (hm.trans (Nat.le_succ m)) p
  let T := C.S.toDepth hm p
  let W := (operation C p m).ratio
  change S.embed i = W.embed (T.embed i)
  rw [Ratio.embed, show T.embed i = wrap _ (T.count.val • Lattice.lift i) from rfl,W.embed_wrap,
    smul_smul, Work.B15.count_trans W T S]

private lemma copy_advance {m p t : ℕ} (h : t ≤ m) (f : Config G (C.side m p) → ℂ) (hp : Envelope f)
    (β : ℝ) (i : Site (C.side t p)) :
    back (operation C p m) β ((center C.S p h 0).copy i f) = (center C.S p (h.trans (Nat.le_succ m)) 0).copy i
      (back (operation C p m) β f) := by
  classical
  let T := center C.S p h 0
  let Q := center C.S p (h.trans (Nat.le_succ m)) 0
  let S := operation C p m
  have ht := transfer_shift S hp (step_approved ..) β (T.omega i) (T.translateBy i)
  have hh : Q.translateBy i=_ := copy_step C p m h i
  change back S β (T.copy i f)=Q.copy i _
  have hb n (A : Tiling n) (g : Config G n→ℂ) (i : A.Cell) :
      A.copy i g= (if A.hand i then fun u => star ((g ∘ Lattice.pull (A.omega i) (A.translateBy i)) u) else
        g ∘ Lattice.pull (A.omega i) (A.translateBy i)) := by
    funext u; by_cases h : A.hand i <;> simp [Tiling.copy,h]
  rw [hb,hb,show Q.omega i=T.omega i from rfl, hh]
  split
  · rename_i hv; rw [if_pos (show Q.hand i from hv),conjugate_back,ht]
  rename_i hv; rw [if_neg (show ¬Q.hand i from hv),ht]

lemma stack_copy (h : k ≤ m) (hp : Envelope F) {t} (ht : t ≤ k) (i : Site (C.side t p)) :
    stack C p N k m ((center C.S p ht 0).copy i F) h = (center C.S p (ht.trans h) 0).copy i (stack C p N k m F h) := by
  induction m,h using Nat.le_induction with
  | base => rw [stack_origin,stack_origin]
  | succ m h ih => rw [stack_step C _ _ _ _ _ h, ih, stack_step C _ _ _ _ _ h,copy_advance C _ _ (stack_envelope C _ _ _ _ _ h hp)]

lemma stack_sub (h : k ≤ m) (F' : Config G (C.side k p)→ℂ) (hp : Envelope F) (ht : Envelope F') :
    stack C p N k m (F-F') h=stack C p N k m F h-stack C p N k m F' h := by
  induction m,h using Nat.le_induction with
  | base => rw [stack_origin,stack_origin,stack_origin]
  | succ m h ih =>
    rw [stack_step C _ _ _ _ _ h,ih,stack_step C _ _ _ _ _ h,stack_step C _ _ _ _ _ h]
    funext U; simp_rw [back, Pi.sub_apply,smul_sub]; rw [integral_sub
      (pull_int (operation C p m) (stack_envelope C _ _ _ _ F h hp) (step_approved ..) ..)
      (pull_int (operation C p m) (stack_envelope C _ _ _ _ F' h ht) (step_approved ..) ..)]; rfl

lemma stack_constant (h : k≤m) (x : ℂ) : stack C p N k m (fun _ => x) h=fun _ => x := by
  induction m,h using Nat.le_induction with
  | base => rw [stack_origin]
  | succ m h ih => rw [stack_step C _ _ _ _ _ h,ih]; exact back_constant _ (step_approved ..) ..
lemma stack_bar (h : k≤m) : stack C p N k m (fun x => star (F x)) h=fun U => star (stack C p N k m F h U) := by
  induction m,h using Nat.le_induction with
  | base => rw [stack_origin,stack_origin]
  | succ m h ih => rw [stack_step C _ _ _ _ _ h,ih,stack_step C _ _ _ _ _ h,conjugate_back]

/-- Each verifier i uses the same centered h cell through every level. We can
iterate conditional independence on ACTUAL back integrations. For offset
constant functions at the coarse end, one per copy, include that in its
argument already here. -/
theorem stack_product {t} (ht : t ≤ k) (r : ℕ) (hK : k ≤ N) (U : Site (C.side t p) → Config G (C.side k p) → ℂ)
    (hp : ∀ i, Interior (region (C.side k p) r) (U i))
    (fit : ∀ m, m ≤ N → ∀ h : k ≤ m, region (C.side m p) (advanceSize C k r m) ⊆ (center C.S p (ht.trans h) 0).chamber 0) :
    let T := center C.S p ht 0
    stack C p N k N (fun x => ∏ i, T.copy i (U i) x) hK = fun x => ∏ i,
      (center C.S p (ht.trans hK) 0).copy i (stack C p N k N (U i) hK) x := by
  intro T
  have hu (m : ℕ) (h : k≤m) (hm : m≤N) : stack C p N k m (fun x => ∏ i,T.copy i (U i) x) h =
      fun x => ∏ i, (center C.S p (ht.trans h) 0).copy i (stack C p N k m (U i) h) x := by
    induction m,h using Nat.le_induction with
    | base => simp only [stack_origin]; rfl
    | succ m h ih =>
      let R := center C.S p (ht.trans h) 0
      let V i := R.copy i (stack C p N k m (U i) h)
      have hv i : Interior (R.chamber i) (V i) :=
        R.copies _ ((stack_region C p N k m (U i) h r (hp i)).enlarges (fit _ (by omega) h))
      rw [stack_step C _ _ _ m _ h,ih (by omega)]
      let S := operation C p m
      change back S _ (fun x => ∏ i,V i x)=_
      rw [back_packs S _ _ (fun i => R.chamber i) V ?_ (fun i _ => hv i) (step_approved ..)]
      · funext x; apply Finset.prod_congr rfl; intro i _
        unfold V; rw [stack_step C _ _ _ _ _ h]
        exact congr_fun (copy_advance C (ht.trans h) _ (stack_envelope C _ _ _ _ _ h (borel_bounded (hp i))) _ i) x
      intro i _ j _ h
      exact Set.disjoint_left.mpr fun y hi hj => h ((R.which_chamber hi).symm.trans (R.which_chamber hj))
  exact hu N hK le_rfl
end YM.Next.UVStress

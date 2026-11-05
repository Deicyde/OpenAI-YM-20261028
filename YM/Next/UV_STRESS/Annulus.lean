import YM.Lane.Lease
import YM.Next.UV_STRESS.Invert
import YM.Next.UV_STRESS.Tiles


/-!
# Input estimate at actual shell nodes

Ordinal m for the *node's* grid can be arbitrarily high, compared to the
exterior tiling side/index k. (So choosing an annulus far above a_k and
assuming all shell nodes will be at that same k would not supply this.)
Here outer k is NOT the k of E.L.16318 which is finer. We fold e^h into the estimate;
at that E application the ratio to a_k^h, with that finer k, must still be
paid. Input receipts like `NodeBound` are outstanding. The counterterm is
a true weight-D cylinder at the origin; root uses ACTUAL replicated copies on
same Wilson law. No sheet of continuum readouts as an input.
-/
set_option autoImplicit false
noncomputable section
namespace YM.Next.UVStress
open Function Set Filter MeasureTheory Analysis Extraction Around Table Ward Cells Lattice Wilson
open scoped Topology ContDiff BigOperators
variable {G : Gauge} {C : Family G} {S : Table C.book} {F : Extraction.Order}

/-- y unscaled in lattice `gridPoint m`. Translation shell h=3, rotation h=4. -/
def annulus (e : ℝ) : Set E4 := {x| e/4<‖x‖ ∧ ‖x‖ < 2*e}

variable {d D h k m N p : ℕ}

def fragment (h : ℕ) (e : ℝ) (t : C.book.Ref 4) (v : C.book.Ref d)
    (m : ℕ) (y : Lattice.Cover) (N p : ℕ) (u : C.book.Ref D) (A : Config G (C.side N p)) : ℂ :=
    (e:ℂ)^h * C.seen ⟨4,t⟩ (location C.S m N p y) A * C.seen ⟨d,v⟩ 0 A - C.seen ⟨D,u⟩ 0 A

/-- Single-node product comparison on the **full** replicated array.
The bounds may depend on station, even coefficient bounds per individual y.
Epsilon slack for the resulting root allowed, not after taking absolute
values of unmatched pieces. Offset alignment of the seam is built in. -/
structure NodeBound (C : Family G) (F : Extraction.Order) (D h k : ℕ) {d : ℕ}
    (e ε : ℝ) (J : Axis → Axis → C.book.Ref 4) (v : C.book.Ref d) : Prop where
  live (i j : Axis) (m : ℕ) (y : Cover) (he : C.S.gridPoint m y ∈ annulus e) :
    ∃ x : ℕ×ℕ → C.book.Ref D, (∃ A : ℝ,F.late fun N p => ‖x (N,p)‖ ≤ A) ∧ ∀ η : ℝ,0<η →
      F.late fun N p => ∃ hN : k+1≤N,
        let T := terrace C.S k hN p
        let B := fragment (d:=d) (C:=C) (D:=D) h e (J i j) v m y N p (x (N,p))
        Interior (T.chamber 0) B ∧ T.rootTest (C.beta N p) B ≤ ε + η

def ShellBound (F : Extraction.Order) (kD h : ℕ) (v : S.Field d) (J : S.Stress) : Prop :=
    ∃ (B : Axis → Axis → C.book.Ref 4) (V : C.book.Ref d), (∀ i j,S.project 4 (B i j)=J i j) ∧
      S.project d V=v ∧ ∀ l : ℕ, ∃ k≥l,∀ ε : ℝ,0<ε → ∀ δ : ℝ,0<δ →
        ∃ e : ℝ,0<e ∧ e≤δ ∧ NodeBound C F kD h k (d:=d) e ε B V

structure Probed (F : Extraction.Order) (J : S.Stress) : Prop where
  tr (d : ℕ) (v : S.Field d) : ShellBound F (d+1) 3 v J
  ro (d : ℕ) (v : S.Field d) : ShellBound F d 4 v J

section grid

structure Watch (C : Family G) where
  n : ℕ
  t : ℕ -- grid level
  x : Fin n → Cover
  q : Fin n → C.book.Token
  wild : Extraction.Order.grid C t (Fin.cons (α:=fun _ => Cover) 0 x) ∈ generic _

lemma location_origin (S : Schedule) (k N p : ℕ) : location S k N p 0 = 0 := by
  unfold location; split
  · rw [map_zero,← Ratio.root_embed,map_zero]
  rfl
namespace Watch
variable (I : Watch C)

def table : Fin (I.n+1) → Cover := Fin.cons 0 I.x
def held : Points (I.n+1) := Extraction.Order.grid C I.t I.table
lemma origin : I.held 0=0 := by ext i; simp [held,table,Extraction.Order.grid,Schedule.gridPoint]
lemma distinct : I.held∈conf _ := generic_conf _ I.wild

def among (N p) : Fin I.n → Site (C.side N p) := fun i => location C.S I.t N p (I.x i)

def plot (N p : ℕ) (U : Config G (C.side N p)) := ∏ i : Fin I.n,C.seen (I.q i) (I.among N p i) U

/-- Against an additional count of fine step errors, still pointwise and
not yet being integrated in y at all. -/
lemma planted (hp : C.Makes) (h : CellHyp C F) (k : ℕ) (hg : I.t≤k) :
    ∃ B : ℝ, 0≤B ∧ ∀ᶠ i : ℕ×ℕ in F.fuse, ∃ hN : k+1 ≤ i.1,
      ∀ f : Config G (C.side i.1 i.2) → ℂ,
      let T := terrace C.S k hN i.2
      Interior (T.chamber 0) f →
      ‖moment (C.beta i.1 i.2) (fun x => f x * I.plot i.1 i.2 x)‖ ≤ T.rootTest (C.beta i.1 i.2) f * B := by
  classical
  have hY := C.S.shrinks.const_mul (9:ℝ)
  rw [mul_zero] at hY
  obtain ⟨j, ⟨A,hA,H⟩, hj, hs⟩ := ((grows h I.q).and ((eventually_ge_atTop (k+1)).and
    (hY.eventually (ge_mem_nhds (C.S.a_pos k))))).exists
  let z := pushSite C.S hg ∘ I.table
  have hD : Injective z := by
    intro i j hx
    apply I.distinct
    change C.S.gridPoint I.t (I.table i)=C.S.gridPoint I.t (I.table j)
    rw [← finer C.S hg (I.table i), ← finer C.S hg (I.table j)]
    exact congr_arg _ (show pushSite C.S hg (I.table i) = _ from hx)
  refine ⟨A^I.n,pow_nonneg hA _,?_⟩
  have he : ∀ᶠ i : ℕ×ℕ in F.fuse, Injective ((wrap (C.S.side k i.2)) ∘ z) := by
    rw [Extraction.Order.fused,Extraction.Order.late]
    exact (F.per.cofinal.eventually (sparse C.S k z hD)).mono fun r hr => Eventually.of_forall fun s => hr
  have ht : ∀ᶠ i in F.fuse,imageBudget I.q A j i.1 i.2 := H
  filter_upwards [he,ht] with i hh hg'
  obtain ⟨N,p⟩ := i; let X := C.side N p
  have hq : j≤N := hg'.1
  let T := terrace C.S k (hj.trans hq) p
  let g (s : Fin (I.n+1)) : T.Cell := wrap (C.S.side k p) (z s)
  let d := 3 * Cells.span C.S hq p
  have hd : d≤T.side.val/3 := by
    apply (Nat.le_div_iff_mul_le (by decide)).2; apply (Nat.cast_le (α:=ℝ)).1
    apply le_of_mul_le_mul_left _ (C.S.a_pos N)
    rw [show C.S.a N * T.side.val=C.S.a k from C.S.embeds_scale T.units]
    unfold d; push_cast; convert hs using 1
    rw [← C.S.embeds_scale (C.S.toDepth hq p)]; ring
  have hv s : I.among N p s ∈ T.margin (g s.succ) d := by
    unfold among; rw [← location_down C.S hg (by omega) (I.x s)]
    exact Lease.fewer T _ hd (buffered C.S k (hj.trans hq) p (pushSite C.S hg (I.x s)))
  choose U hU hQ hB using fun (s : Fin I.n) =>
    Lease.alive (T:=T) hp s (I.among N p s) hg' hq (inherits (by omega : k≤j) hq) (hv s)
  refine ⟨hj.trans hq,fun f hm => ?_⟩
  let D : Fin (I.n+1) → Config G X → ℂ := Fin.cons f U
  have hi : ∀ (i : Fin (I.n+1)), Interior (T.chamber 0) (D i) := Fin.cases hm hQ
  have hw (x) : (∏ i : Fin (I.n+1), T.copy (g i) (D i) x)= f x * I.plot N p x := by
    have hi : g 0=0 := by dsimp only [g,z, Function.comp_apply]; rw [table, Fin.cons_zero,pushSite,smul_zero,map_zero]; rfl
    rw [Fin.prod_univ_succ,hi,T.copy_zero]; congr 1
    exact Finset.prod_congr rfl fun j _ => congr_fun (hU j) x
  let β := C.beta N p
  have hx := T.planted (h.all _ _) g hh D hi
  simp_rw [hw] at hx
  apply hx.trans; rw [Fin.prod_univ_succ]
  refine mul_le_mul_of_nonneg_left ?_ (T.root_nonneg β f)
  calc
    _ ≤ ∏ _ : Fin I.n,A := Finset.prod_le_prod (fun i _ => T.root_nonneg β (U i)) (fun i _ => hB i)
    _ = _ := by simp
end Watch
end grid

section nodes
namespace Watch
variable (I : Watch C) (m : ℕ) (x : Cover)

def point := Points.cons (C.S.gridPoint m x) I.held
def cuts (N p : ℕ) : Fin (I.n+1) → Site (C.side N p) := Fin.cons (α:=fun _ => Site _) 0 (I.among N p)
def layers (N p : ℕ) : Fin (I.n+2) → Site (C.side N p) := Fin.cons (location C.S m N p x) (I.cuts N p)

lemma single_lim (v : C.book.Token) (hp : F.PointLimits C S) :
    Tendsto (fun u : ℕ×ℕ => C.numeric u.1 u.2 (Fin.cons (α:=fun _ => C.book.Token) v I.q) (I.cuts u.1 u.2)) F.fuse
      (𝓝 (S.read I.held (Fin.cons (α:=fun _ => C.book.Token) v I.q))) := by
  refine (Extraction.Order.along (Cells.eventual_grid C F S hp I.table I.wild
    (Fin.cons (α:=fun _ => C.book.Token) v I.q))).congr (fun u => ?_)
  apply congr_arg (C.numeric _ _ _)
  ext1 i; refine Fin.cases (by simp [table,location_origin,cuts]) (fun j => ?_) i
  simp [among,table,cuts]

lemma placed (v w : C.book.Token) (hp : F.PointLimits C S) (hv : I.point m x ∈ generic _) :
    Tendsto (fun u : ℕ×ℕ => C.numeric u.1 u.2
      (Fin.cons (α:=fun _ => C.book.Token) v (Fin.cons (α:=fun _ => C.book.Token) w I.q)) (I.layers m x u.1 u.2)) F.fuse
      (𝓝 (S.read (I.point m x) (Fin.cons (α:=fun _ => C.book.Token) v (Fin.cons (α:=fun _ => C.book.Token) w I.q)))) := by
  let k := max I.t m
  let U := Fin.cons (α:=fun _ => Cover) (pushSite C.S (le_max_right I.t m) x) (pushSite C.S (le_max_left I.t m) ∘ I.table)
  let W := Fin.cons (α:=fun _ => C.book.Token) v (Fin.cons (α:=fun _ => C.book.Token) w I.q)
  have he : I.point m x = Extraction.Order.grid C k U := by
    ext1 i; refine Fin.cases ?_ (fun j => ?_) i
    · unfold point Points.cons Extraction.Order.grid; simp only [U,k,points_apply,Fin.cons_zero]; rw [finer]
    unfold point Points.cons Extraction.Order.grid held; simp [U,k,Extraction.Order.grid,finer]
  rw [he] at hv ⊢
  refine (Extraction.Order.along (Cells.eventual_grid C F S hp U hv W)).congr' ?_
  filter_upwards [large_mesh F k] with i hi
  apply congr_arg (C.numeric _ _ W); ext1 l; refine Fin.cases ?_ (fun j => ?_) l
  · simp only [U,Fin.cons_zero,layers]; exact location_down C.S (le_max_right I.t m) hi _ _
  simp only [U,Fin.cons_succ,layers,cuts,Function.comp_apply]; rw [location_down C.S _ hi]
  refine Fin.cases (by simp [table,location_origin]) (fun j => ?_) j; simp [table,among]

private lemma fragment_integral (v : C.book.Ref 4) (w : C.book.Ref d) (z : C.book.Ref D)
    (N p h : ℕ) (e : ℝ) :
    moment (C.beta N p) (fun A => fragment (C:=C) (d:=d) (D:=D) h e v w m x N p z A * I.plot N p A) =
      (e:ℂ)^h * C.numeric N p
        (Fin.cons (α:=fun _ => C.book.Token) ⟨4,v⟩ (Fin.cons (α:=fun _ => C.book.Token) ⟨d,w⟩ I.q)) (I.layers m x N p)-
          C.numeric N p (Fin.cons (α:=fun _ => C.book.Token) ⟨D,z⟩ I.q) (I.cuts N p) := by
  unfold moment; rw [C.num,C.num,← integral_const_mul,← integral_sub
    ((C.integrableR _ _).const_mul _) (C.integrableR _ _)]
  apply integral_congr_ae; filter_upwards with A
  rw [fragment, plot]
  nth_rw 2 [Fin.prod_univ_succ]
  -- explicitly order
  simp only [layers,cuts,Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ,mul_assoc]
  ring

/-- Limit of the genuine signed comparison. Coefficients can vary with
cutoffs (NeBot subfilter used ONLY in checking continuum estimates).
-/
lemma cost_limit (F : Extraction.Order) (v : C.book.Ref 4) (w : C.book.Ref d)
    (hp : F.PointLimits C S) (H : S.Hierarchy) {f : Filter (ℕ×ℕ)} [f.NeBot] (hb : f ≤ F.fuse)
    (hv : I.point m x ∈ generic _) (h : ℕ) (e : ℝ) {V : ℕ × ℕ → C.book.Ref D} {p : C.book.Ref D} (ht : Tendsto V f (𝓝 p)) :
    let q := S.classTokens ∘ I.q
    Tendsto (fun u : ℕ×ℕ => moment (C.beta u.1 u.2) (fun A => fragment (C:=C) (d:=d) (D:=D)
      h e v w m x u.1 u.2 (V u) A * I.plot u.1 u.2 A)) f
      (𝓝 ((e:ℂ)^h * disc (Fin.cons ⟨4,S.project 4 v⟩ (Fin.cons ⟨d,S.project d w⟩ q)) (I.point m x) -
        disc (Fin.cons ⟨D,S.project D p⟩ q) I.held)) := by
  intro q
  let first (v : C.book.Token) := Fin.cons (α:=fun _ => C.book.Token) v I.q
  let second (v' w' : C.book.Token) := Fin.cons (α:=fun _ => C.book.Token) v' (first w')
  have he := I.placed m x ⟨4,v⟩ ⟨d,w⟩ hp hv |>.mono_left hb
  have hh : Tendsto (fun u : ℕ×ℕ => C.numeric u.1 u.2 (first ⟨D,V u⟩) (I.cuts u.1 u.2)) f
      (𝓝 (S.read I.held (first ⟨D,p⟩))) := by
    let g (u : ℕ×ℕ) := C.ensemble (readDegrees (v:=I.q) D) (I.cuts u.1 u.2)
    have hx (a : C.book.Ref D) (u : ℕ×ℕ) : C.numeric u.1 u.2 (first ⟨D,a⟩) (I.cuts u.1 u.2)= g u (vals I.q a) := by
      rw [show first ⟨D,a⟩=(fun i => (⟨readDegrees (v:=I.q) D i,vals I.q a i⟩ : C.book.Token)) from ?_]; rfl
      funext i; refine Fin.cases (show first _ 0 = _ from (by rw [show first ⟨D,a⟩ 0=⟨D,a⟩ from Fin.cons_zero ..]; rfl)) (fun j => ?_) i
      unfold first; rw [Fin.cons_succ]; rfl
    let L (u : ℕ×ℕ) := LinearMap.toContinuousLinearMap
      (show C.book.Ref D→ₗ[ℂ] ℂ from (g u).toLinearMap (vals I.q (0:C.book.Ref D)) 0)
    have hy (a : C.book.Ref D) (u : ℕ×ℕ) : L u a = C.numeric u.1 u.2 (first ⟨D,a⟩) (I.cuts u.1 u.2) := by
      rw [hx]; change g u (update (vals I.q (0:C.book.Ref D)) 0 (headValue I.q a))=_; rw [← update_front]
    have hz (a : C.book.Ref D) : Tendsto (fun u : ℕ×ℕ => (L u).toLinearMap a) f (𝓝 (S.injectFront I.q I.held D a)) :=
      ((I.single_lim ⟨D,a⟩ hp).mono_left hb).congr fun u => (hy a u).symm
    exact (Dash.arcing (Dash.fit_plane (fun u => (L u).toLinearMap) (S.injectFront I.q I.held D) hz) ht).congr (fun u => hy _ _)
  have hq : S.read (I.point m x) (second ⟨4,v⟩ ⟨d,w⟩) =
      disc (Fin.cons ⟨4,S.project 4 v⟩ (Fin.cons ⟨d,S.project d w⟩ q)) (I.point m x) := by
    rw [← S.at_project S H.laws.toSymmetric (fun _ => le_rfl) (generic_conf _ hv)]; unfold second first; rw [Work.A01.comp_cons, Work.A01.comp_cons]; rfl
  have hf : S.read I.held (first ⟨D,p⟩)=disc (Fin.cons ⟨D,S.project D p⟩ q) I.held := by
    rw [← S.at_project S H.laws.toSymmetric (fun _ => le_rfl) I.distinct]; unfold first; rw [Work.A01.comp_cons]; rfl
  rw [← hf, ← hq]; exact ((he.const_mul ((e:ℂ)^h)).sub hh).congr (fun u => (I.fragment_integral ..).symm)
end Watch
end nodes
end YM.Next.UVStress

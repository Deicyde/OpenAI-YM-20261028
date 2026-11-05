import YM.OPE.Eye.Civic
import YM.OPE.Prices.Space

/-!
# Take the grid matching sublimit

Fits along many-copy capture. The bound on the *same* match can be used
against any exterior priced by this grid (or another one with
admissible widths). Keep the `Survival` predicate precisely, in particular
the underlying filter, geometry and sector cost at the actual k rather
than just reference-norm compactness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE
open MeasureTheory Function Filter Set Lattice RG Wilson Cells Extraction Word Spec
open MergeProof Ribbons Accent ManyCopies Next.Rank Station Next.UVStress
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book} (U : Final C F S)
variable {I J : Type}[Fintype I][DecidableEq I][Fintype J] {A A' : ℝ}
variable {x:I→ Cover} {k k' d m:ℕ}{c: ℝ}{v:I→ C.book.Token}
set_option quotPrecheck false
local notation "Y"=> C.path.levels
local notation "H"=> C.path.levels.budget
local notation "X"=> C.S.gridPoint k'
-- fit selected prices
structure Plot (C:Family G) (k m k':ℕ)(x:I→ Cover) : Prop where
   fit : ∀ i,8*‖C.S.gridPoint k' (x i)‖< C.S.a (m+1)
   spaced : Apart (2*C.S.a k' * ((C.path.levels.budget k').B:ℝ)^2) (C.S.gridPoint k' ∘ x)
   first : k ≤ m
   last : m+1 ≤ k'
lemma Plot.marsh (h:Plot C k m k' x) : ∀ᶠ p:ℕ in atTop, let f:=(wrap (C.side k' p)) ∘ x;
    Edition.Spaced (H k').B f ∧ ∀ i,loops C k' p (f i) (m+1)=0 ∧ C.S.place (f i)= (X) (x i) := by
    filter_upwards [(eventually_all.mpr fun i=> faraway C k' (x i)), (eventually_all.mpr (fun i=>eventually_all.mpr (fun j=> Cards.native_space (k:=k') C (x i) (x j))))] with p hx hp -- p param?
    intro f
    constructor
    · intro i j hij; let t:= separation (f i) (f j); have he :2*C.S.a k'*(( (H k').B:ℝ)^2) < 2*(C.S.a k'*t):=(h.spaced i j hij).trans_le (hp i j)
      exact_mod_cast (le_of_mul_le_mul_left (show (2*C.S.a k')*((H k').B:ℝ)^2 ≤ (2*C.S.a k')*t by linarith only [he]) (mul_pos two_pos (C.S.a_pos _)))
    intro i; let Z:= C.S.toDepth h.last p; refine ⟨?_,hx i⟩; rw [vote C k' p (m+1) (f i) h.last]; apply Station.owner; rw [show Z.embed 0=0 from Z.root.map_zero];
    have he := normC C k' p (f i)|>.1; rw [(show C.S.place (f i)= _ from hx i)] at he; have hu:= h.fit i; rw [← C.S.embeds_scale Z] at hu; exact_mod_cast (lt_of_mul_lt_mul_left (show C.S.a k'*(2*(separation (f i) 0:ℝ))< C.S.a k'*Z.count.val by linarith [he,hu,norm_nonneg (C.S.gridPoint k' (x i))]) (C.S.a_pos k'|>.le))
-- PriceAt k layout at origin
structure Survival (F: Extraction.Order)(k m k' : ℕ)(A c:ℝ)(v:I→ C.book.Token)(x:I→ Cover)(d:ℕ)(q:C.label d): Prop where
   reference : C.ref d ≤ m
   wins : ∃ (u: Filter (ℕ×ℕ)) (f:ℕ×ℕ → C.label d), u.NeBot ∧ u≤ F.fuse∧ Tendsto f u (𝓝 q)∧ Remains (C:=C) v u k' k d x f A ∧ ∀ᶠ i in u,quota C d m i.1 i.2 (f i) ≤ c
local notation "P0"=> PriceAt C c A d (fun i=> (v i).1) (fun i=>(v i).2) k m k'
include U
lemma price_plot (h:P0)(hx:Plot C k m k' x): ∃ q, Survival (C:=C) F k m k' A c v x d q:=by
    let g := germ (frozen C v); let S (N p:ℕ) (q:C.label d):= Cards.PaidAt C.S N p k (C.beta N p) A (Cards.register C k' x g N p-C.O N p q 0); let t (i:ℕ×ℕ)(q:C.label d):=S i.1 i.2 q∧ quota C d m i.1 i.2 q ≤ c
    have hp:= U.room.cutoff
    have he : ∀ᶠ i in F.fuse,∃ q,t i q:=by
       rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [F.per.cofinal.eventually hx.marsh] with p hp'
       have hd := F.mesh.cofinal; let j:=F.per p
       filter_upwards [hd.eventually (near_center C k d hp), eventually_all.mpr (fun i=>hd.eventually (near_center C k (v i).1 hp)), hd.eventually_gt_atTop k'] with N hN he hk
       let n:= F.mesh N; let r:=(wrap (C.side k' j)) ∘ x; have hk:k' < n:= hk; have ht:k≤n:= hx.first.trans (m.le_succ.trans (hx.last.trans hk.le)); let T:= (center C.S j ht 0); let f(i):= C.O n j (d:=(v i).1) (v i).2 ((C.S.toDepth hk.le j).embed (r i));
       have hv: Edition.Spaced (H k').B r∧ ∀ i,loops C k' j (r i) (m+1)=0 ∧ C.S.place (r i)=X (x i):= hp';
       have hV(i:I):Interior (T.chamber 0) (f i):=he i ht j _ ((show 8*‖C.S.place ((C.S.toDepth hk.le j).embed (r i))‖≤ C.S.a k from ?_)) _
       swap -- nested have `?_` not produces goal? try
       · rw [C.S.embeds_place,(hv.2 i).2]; exact (hx.fit i|>.le).trans (C.S.strictAnti.antitone (hx.first.trans m.le_succ))
       have hu (x:C.label d): Interior (T.chamber 0) (C.O n j x 0) := hN ht j _ (by rw [latzero]; simp [(C.S.a_pos k).le]) _
       obtain ⟨z,hA,hP,hU⟩:= h.quote n j hk ht r (fun i=> (hv.2 i).1) hv.1 hV hu
       have hh: Cards.register C k' x g n j=(fun U=> ∏ i,f i U):= by funext U; rw [germ_here]; dsimp only [f]; simp_rw [Cells.location,dif_pos hk.le]; rfl
       refine ⟨z,?_⟩; change S n j z ∧ _; unfold S; rw [hh]; exact ⟨⟨ht,hP,hU⟩,hA⟩
    let Y' (i:ℕ×ℕ):C.label d:= if p:∃ q,t i q then p.choose else 0; have he:∀ᶠ i in F.fuse,t i (Y' i):= he.mono (fun i h=> by unfold Y'; rw [dif_pos h]; exact h.choose_spec)
    obtain ⟨Q,hQ,hI⟩ := quota_stop C hp h.step; obtain ⟨l,hl,hX,u,hY⟩:= finite_extract (𝓛:=F.fuse) Y' (Q*c) (by filter_upwards [he,(Cards.largeMesh F).eventually_ge_atTop m] with i hi hm using (hI i.1 i.2 (Y' i) hm).trans (mul_le_mul_of_nonneg_left hi.2 hQ))
    exact ⟨u,h.step,l,Y',hX,hl,hY,⟨(he.mono fun _ h=> h.1).filter_mono hl⟩,(he.mono fun _ h=>h.2).filter_mono hl⟩
end YM.OPE

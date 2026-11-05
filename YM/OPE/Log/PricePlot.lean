import YM.OPE.Log.Spill
import YM.OPE.Prices.Space

/-!
# Take the grid matching sublimit

Fits along many-copy capture. The bound on the *same* match can be used
against any exterior priced by this grid (or another one with
admissible widths). Keep the `Dress` predicate precisely, in particular
the underlying filter, geometry and sector cost at the actual k rather
than just reference-norm compactness.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Log
open MeasureTheory Function Filter Set Lattice RG Wilson Cells Extraction Word Spec
open MergeProof Ribbons Accent ManyCopies Next.Rank Station Next.UVStress
open scoped Topology BigOperators Classical Matrix.Norms.Frobenius ContDiff
variable {G:Gauge}{C:Family G}{F: Extraction.Order}{S:Table C.book} (U : Final C F S)
variable {I J : Type}[Fintype I][DecidableEq I][Fintype J] {A A' : ℝ}
variable {x:I→ Cover} {k k' d m:ℕ}{c: ℝ}{v:I→ C.book.Token}
-- PriceAt k layout at origin
structure Dress (𝓕:Filter (ℕ×ℕ)) (S:Table C.book)(k m k' : ℕ)(A c:ℝ)(v:I→ C.book.Token)(x:I→ Cover)(d:ℕ)(q:C.label d): Prop where
   reference : C.ref d ≤ m
   wins : ∃ (u: Filter (ℕ×ℕ)) (f:ℕ×ℕ → C.label d), u.NeBot ∧ u≤𝓕∧ Tendsto f u (𝓝 q)∧ (∃ w:I→ C.book.Token,S.classTokens ∘ w=S.classTokens ∘ v ∧ ∃ Y:ReadLabel C w, (∀ i,Tendsto (Y i) u (𝓝 (w i).2))∧Stylus Y u k' k d x f A)∧ ∀ᶠ i in u,quota C d m i.1 i.2 (f i) ≤ c
include U
lemma price_plot_M {Q:I→ℝ}(h: ShortPrice C c A Q d (fun i=>(v i).1) k m k')(s:(i:I)→ C.label (v i).1){Y:ReadLabel C v}{𝓕:Filter (ℕ×ℕ)} [𝓕.NeBot] (hr:𝓕≤F.fuse)(hs:∀ i,Tendsto (Y i) 𝓕 (𝓝 (s i)))(hV:∀ i,S.project (v i).1 (s i)=S.project (v i).1 (v i).2)(hQ:∀ i:I,∀ᶠ N in 𝓕, Next.UVStress.quota C (v i).1 k' N.1 N.2 (Y i N) ≤ Q i)(hx:Plot C k m k' x): ∃ q, Dress (C:=C) 𝓕 S k m k' A c v x d q:=by
    let g := germ Y; let E (N p:ℕ) (q:C.label d):= Cards.PaidAt C.S N p k (C.beta N p) A (Cards.register C k' x g N p-C.O N p q 0); let t (i:ℕ×ℕ)(q:C.label d):=E i.1 i.2 q∧ quota C d m i.1 i.2 q ≤ c
    have hp:= U.room.cutoff
    have hT := (Cards.largeMesh F).mono_left hr
    have hP:Tendsto Prod.snd F.fuse atTop:=tendsto_atTop.mpr fun i=>by
       rw [Extraction.Order.fused,Extraction.Order.late]; filter_upwards [F.per.cofinal.eventually_ge_atTop i] with p hp; exact Eventually.of_forall (fun j=>hp)
    have he : ∀ᶠ i in 𝓕,∃ q,t i q:=by
       filter_upwards [(hP.eventually hx.marsh).filter_mono hr, hT.eventually (near_center C k d hp), eventually_all.mpr (fun i=>hT.eventually (near_center C k (v i).1 hp)), hT.eventually_gt_atTop k', eventually_all.mpr hQ ] with Z hp' hN he hk hQ
       let n:= Z.1; let j:= Z.2; let u(i:I):=Y i Z; let r:=(wrap (C.side k' j)) ∘ x; have hk:k' < n:= hk; have ht:k≤n:= hx.first.trans (m.le_succ.trans (hx.last.trans hk.le)); let T:= (center C.S j ht 0); let f(i):= C.O n j (d:=(v i).1) (u i) ((C.S.toDepth hk.le j).embed (r i));
       have hv: Edition.Spaced (C.path.levels.budget k').B r∧ ∀ i,loops C k' j (r i) (m+1)=0 ∧ C.S.place (r i)= C.S.gridPoint k' (x i):= hp';
       have hV(i:I):Interior (T.chamber 0) (f i):=he i ht j _ ((show 8*‖C.S.place ((C.S.toDepth hk.le j).embed (r i))‖≤ C.S.a k from ?_)) _
       swap -- nested have `?_` not produces goal? try
       · rw [C.S.embeds_place,(hv.2 i).2]; exact (hx.fit i|>.le).trans (C.S.strictAnti.antitone (hx.first.trans m.le_succ))
       have hu (x:C.label d): Interior (T.chamber 0) (C.O n j x 0) := hN ht j _ (by rw [latzero]; simp [(C.S.a_pos k).le]) _
       obtain ⟨z,hA,hP,hU⟩:= h.quote n j hk ht u r hQ (fun i=> (hv.2 i).1) hv.1 hV hu
       have hh: Cards.register C k' x g n j=(fun U=> ∏ i,f i U):= by funext U; rw [germ_here]; dsimp only [f]; simp_rw [Cells.location,dif_pos hk.le]; rfl
       refine ⟨z,?_⟩; change E n j z ∧ _; unfold E; rw [hh]; exact ⟨⟨ht,hP,hU⟩,hA⟩
    let Y' (i:ℕ×ℕ):C.label d:= if p:∃ q,t i q then p.choose else 0; have he:∀ᶠ i in 𝓕,t i (Y' i):= he.mono (fun i h=> by unfold Y'; rw [dif_pos h]; exact h.choose_spec)
    obtain ⟨Q,hQ,hI⟩ := quota_stop C hp h.step; obtain ⟨l,hl,hX,u,hY⟩:= finite_extract (𝓛:=𝓕) Y' (Q*c) (by filter_upwards [he,hT.eventually_ge_atTop m] with i hi hm using (hI i.1 i.2 (Y' i) hm).trans (mul_le_mul_of_nonneg_left hi.2 hQ))
    exact ⟨u,h.step,l,Y',hX,hl,hY,⟨fun i=>⟨(v i).1,s i⟩, funext (fun i=>show S.classTokens _=S.classTokens _ from congr_arg (fun x=> Sigma.mk (v i).1 x) (hV i)), Y, fun i=>(hs i).mono_left hl,⟨(he.mono fun _ h=> h.1).filter_mono hl⟩⟩,(he.mono fun _ h=>h.2).filter_mono hl⟩
end YM.OPE.Log

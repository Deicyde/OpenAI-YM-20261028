import YM.OPE.Nesting.Composite

/-! At an ancestor with strict internal edges, replacing them all through
some auxiliary horizons H_j almost perfectly agrees with its original
reading. The H_j can be taken **fixed per child** (not per series term), so
its partial sum through any of the demanded smaller horizons will be visible.
The ingredients are `Fusion.tariff` at full strength wrt the exteriors.
There is still no power scale assigned to a particular phase of the physical
theory. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Composite
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)(h:Services C F S)
variable {L:Type}{l:Filter L}[l.NeBot]{T:L→ℝ} (hT:Tendsto T l atTop)
variable {N:ℕ}{g:Fin N→Tree}{z:Envelope L (fork N g)}(v:(fork N g).Leaf→S.Tag){a:(fork N g).Inner→ℝ}{κ:ℝ}
       (hg:Regular l T (fork N g) κ a z) (ht:∀ i,g i≠bud→ a (Sum.inl ()) < (g i).topAge (a (Sum.inl ())) (childAge i a))
include h hT hg ht
lemma escape (γ:ℝ){m:ℕ}(j:R.channels m)(D:Fin N→ℕ):∃ H:Fin N→ℕ, D ≤ H ∧ RateLE l T (fun s=> (Menu.raw z v).charge R m j (Tree.center z) s - hinge U R z v H j s) γ:=by
    let p:= Fusion.Children (z:=z) v; let k:=a (Sum.inl ())
    have hx i:=Fusion.tariff U R hT h _ _ _ _ (Tree.childWages i v) (hg.inside i)
    choose b₀ hb h₀ using fun j=>(hx j).1.clients
    obtain ⟨B,hB⟩:=(finite_range b₀).bddAbove; obtain ⟨W,hW⟩:= Sensor.roomFor U R m
    let c:=max k B
    have hB j:b₀ j ≤ c := (hB (mem_range_self j)).trans (le_max_right ..)
    have hp(j):Eligible l T (down j z) c (p j):=(h₀ j _ (hB j)).1
    let mnu(i)(H):=beacon U R H (Tree.down i z) (Tree.childWages i v)
    let good(i:Fin N)(q:Menu S L) := Eligible l T (down i z) c q ∧ ∃ H:ℕ,D i ≤ H ∧ q=mnu i H
    have hs(i:Fin N)(W' r':ℝ): ∃ q,good i q ∧ Eligible l T (down i z) c q ∧ Agrees U l T (down i z) k c W' r' (p i) q:= by
       by_cases hi:g i=bud
       · exact ⟨p i,⟨hp i,⟨D i,le_refl _,(flash_bud U R hi).symm⟩⟩,hp i,Agrees.self U⟩
       obtain ⟨H,h_big,h_,h_q⟩:=high U R _ ((hx i).2) (hg.inside i) (rfl) (ht i hi) (le_max_left _ B) W' r' (D i)
       let q:= (loadedRaw U R (down i z) (childWages i v) (Tree.center (down i z)) H)
       have he: mnu i H=q:= beacon_native U R hi
       refine ⟨q,⟨h_.earns (le_max_left ..),H,h_big,he.symm⟩,h_.earns (le_max_left ..),h_q⟩
    obtain ⟨A,hA,h₂⟩:= sequential U (W:=W) (r:=γ) p good hg (le_max_left _ B) hT hp hs
    obtain ⟨hraw,hf⟩:=Fusion.raw_fusion U (W:=W) (r:=γ) hT v hg hp (le_max_left _ B)
    choose H h_ hH using fun j=>(hA j).2
    refine ⟨H,h_,(?_ : RateLE l T (fun s=>(Menu.raw z v).charge R m j (Tree.center z) s-(Menu.fuse A).charge R m j (Tree.center z) s) γ).congr (Eventually.of_forall (fun s=>?_))⟩
    · exact Sensor.remit U R _ _ j (hW _ le_rfl) hT (fun {_} {_} w => by apply Agrees.then U hT (by apply hf) (by apply h₂)) hraw (Eligible.products A injective_id hT (fun j=>(hA j).1) (le_max_left _ B) hg) hg.vanish hg.nonneg (le_max_left _ B)
    dsimp only; apply congr_arg (_-·) (?_); rw [show A=lamps (z:=z) (v:=v) U R H from funext hH]; exact flash_all ..
end YM.OPE.Nesting.Composite

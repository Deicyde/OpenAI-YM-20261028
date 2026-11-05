import YM.OPE.Nesting.Reload

/-!
# Fusion on all logarithmic plateaux

When a child's log-time is comparable to the parent's, flatten all its
currently comparable slots. At the other children spend **full discrepancy**
at an auxiliary horizon so large that one gets a gain to arbitrary desired
precision. Telescope in a triangular order: later switch costs see previous
auxiliary outputs (already fixed), not the reverse. Thus even for
super-power-hierarchical scales relative to the root, direct readings and
complete fixed exterior residues are bounded at the claimed prices.
-/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Nesting.Fusion
open Orbits Orbits.Reader Function Filter Extraction Set Table Tree Measures Menu Atom MeasureTheory
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{C:Family G}{F:Order}{S:Table C.book}(U:Spec.Final C F S)
  (R:Reader U.sector.derivatives U.sector.turns U.room.kernel.spin)
variable {L:Type}{l:Filter L}{T:L→ℝ}(hT:Tendsto T l atTop)[l.NeBot]
section Combine
variable {n:ℕ}{f:Fin n→Tree}{z:Envelope L (fork n f)}
variable {κ b W r:ℝ}{a:(fork n f).Inner→ℝ} (v:(fork n f).Leaf→S.Tag)(h:Regular l T (fork n f) κ a z)
local notation "V" => Tree.cost

def Children := fun i:Fin n=> Menu.raw (Tree.down i z) (Tree.childWages i v)
include h
lemma subtree_cost(j:Fin n): V (f j) (Tree.topAge (fork n f) κ a) (childAge j a) (wages (childWages j v))=V (f j) (a (Sum.inl ())) (childAge j a) (childWages j (wages v)):=rfl

include hT

lemma comparable_bundle (P:Fin n→Menu S L) (hP:∀ j,Comparable l T (Tree.down j z) (Tree.topAge (fork n f) κ a) (Tree.cost (f j) (Tree.topAge (fork n f) κ a) (Tree.childAge j a) (wages (Tree.childWages j v))) (P j)):Comparable l T z (Tree.topAge (fork n f) κ a) (V (fork n f) κ a (wages v)) (fuse P) := by
   intro k
   have hQ:= Eligible.products P injective_id hT (fun j=>Comparable.earns (hP j) le_rfl) le_rfl h
   obtain ⟨hz,hk,-⟩:= hQ k
   refine ⟨hz,hk,(RateLE.prod (S:=Finset.univ) hT (fun j _=> (hP j (k j)).2.2)).mono ?_⟩
   rw [Finset.sum_sub_distrib,← Finset.sum_mul]; change (∑ j,Tree.cost (f j) (Tree.topAge (fork n f) κ a) (Tree.childAge j a) (wages (Tree.childWages j v))) - (∑ j:Fin n, ((P j).pick (k j)|>.cost))*(Tree.topAge (fork n f) κ a) ≤ _
   rw [← Atom.bundle_cost]; rfl

include κ
lemma raw_fusion (ht:∀ j,Eligible l T (down j z) b (Children (z:=z) v j)) (hb:(Tree.topAge (fork n f) κ a)≤b):
     Eligible l T z b (Menu.raw z v) ∧ Agrees U l T z (a (Sum.inl ())) b W r (Menu.raw z v) (fuse (Children (z:=z) v)):=by
    let p:= Children (z:=z) v
    have hv(c:(Menu.raw z v).Draw):Eligible l T z b (fuse p):= Eligible.products (a:=κ) p injective_id hT ht hb h -- wrong a name?
    refine ⟨(by intro c; exact ⟨⟨(fork n f).leafSeat,rfl⟩,(hv c (fun _=>())).2.1,0,RateLE.const _ hT⟩),fun w y s _ hx hy=>?_⟩
    let Z:= Menu.raw z v; let Tv:=spectator U ∘ s
    have huniq(i:L): Z.atView Tv y w i = (fuse p).atView Tv y w i:=by
       calc Z.atView Tv y w i = ∑ q:(fuse p).Draw,Z.atView Tv y w i := by symm; convert Fintype.sum_unique (f:=fun _:Fin n→Unit=>Z.atView Tv y w i) using 1; apply Fintype.sum_equiv (Equiv.refl (Fin n→Unit)) _ _ (fun _=>rfl)
            _ = _ := Finset.sum_congr rfl (fun q _=>(Menu.raw_bundle n f z v q Tv y w i).symm)
    change RateLE l T (fun i=> Z.atView Tv y w i-(fuse p).atView Tv y w i) r; simp_rw [huniq,sub_self]; exact RateLE.zero (X:=ℂ) l T r

-- operations at nontrivial parents:
variable
     (supply:∀ j,Supply U l T (down j z) ((f j).topAge (Tree.topAge (fork n f) κ a) (childAge j a)) (Tree.cost (f j) (Tree.topAge (fork n f) κ a) (Tree.childAge j a) (wages (Tree.childWages j v))) (Children (z:=z) v j))
     (ready:∀ j,Meets U R l T (down j z) (Tree.center (down j z)) ((f j).topAge (Tree.topAge (fork n f) κ a) (childAge j a)) (Tree.cost (f j) (Tree.topAge (fork n f) κ a) (Tree.childAge j a) (wages (Tree.childWages j v))) (Children (z:=z) v j))
include U R κ h supply ready
lemma supplies : Supply U l T z (Tree.topAge (fork n f) κ a) (V (fork n f) κ a (wages v)) (Menu.raw z v) := by
    constructor
    choose b₀ h_b rec using fun j=>(supply j).1
    obtain ⟨B,hB⟩:= (finite_range b₀).bddAbove
    refine ⟨max B (Tree.topAge (fork n f) κ a), le_max_right ..,fun b_b h_b' =>?_⟩
    let p:=Children (z:=z) v
    have hB(j):b₀ j≤b_b:= (hB (mem_range_self _)).trans ((le_max_left ..).trans h_b')
    let good(j:Fin n)(A:Menu S L):Prop:=Comparable l T (Tree.down j z) (Tree.topAge (fork n f) κ a) (Tree.cost (f j) (Tree.topAge (fork n f) κ a) (Tree.childAge j a) (wages (Tree.childWages j v))) A
    have hp(j):Eligible l T (down j z) b_b (p j):=(rec j b_b (hB j)).1
    obtain ⟨he,-⟩:=raw_fusion U (W:=0) (r:=0) hT v h hp ((le_max_right ..).trans h_b')
    refine ⟨he, fun W γ=> ?_⟩
    have he' := show Agrees U l T z (Tree.topAge (fork n f) κ a) b_b W γ (Menu.raw z v) (fuse p) from (raw_fusion U hT v h hp ((le_max_right ..).trans h_b')).2
    have hPick(j:Fin n)(W' γ':ℝ):∃ q,good j q ∧ Eligible l T (down j z) b_b q ∧ Agrees U l T (down j z) (Tree.topAge (fork n f) κ a) b_b W' γ' (p j) q := by
      let e:=childAge j a
      rcases (h.inside j).ageLower.eq_or_lt with he|he
      · change (Tree.topAge (fork n f) κ a)=(f j).topAge ((fork n f).topAge κ a) (childAge j a) at he
        obtain ⟨q,hq,he'⟩:= (rec j b_b (hB j)).2 W' γ'
        exact ⟨q,by unfold good; rw [← he] at hq; exact hq, hq.earns ((h_b j).trans (hB j)),by intro J _ w y s hw hv; rw [he] at hv; exact he' w y s hw hv⟩
      let hv:=ready j
      change Meets U R l T (down j z) _ ((f j).topAge (Tree.topAge (fork n f) κ a) e) _ _ at hv; obtain ⟨H,h',hg,hG⟩:=high U R (childWages j v) hv (h.inside j) rfl he ((le_max_right ..).trans h_b') W' γ' 0
      exact ⟨_,hg,hg.earns ((le_max_right ..).trans h_b'), hG⟩
    obtain ⟨B,h₁,h₂⟩:= sequential U (W:=W) (r:=γ) p good h ((le_max_right ..).trans h_b') hT hp hPick
    exact ⟨fuse B, comparable_bundle hT v h B h₁,Agrees.then U hT (@he') h₂⟩
end Combine
local notation "V" => Tree.cost
include hT
section Assembly
variable (h:Services C F S) {t:Tree}{u:ℝ}{a:t.Inner→ℝ}{z:Envelope L t}(v:t.Leaf→S.Tag)
abbrev Cost := Tree.cost t u a (wages v) -- u implicit
include h

lemma bud_supply (u:ℝ)(v:Tree.bud.Leaf→S.Tag)(z:Envelope L Tree.bud)(a:Tree.bud.Inner→ℝ): Supply U l T z u (V Tree.bud u a (wages v)) (Menu.raw z v) :=by
    have h:Comparable l T z u (V Tree.bud u a (wages v)) (Menu.raw z v):= by
        intro k; refine ⟨⟨_,rfl⟩,Kept.sole l T (fun i=> z i ()) u,?_⟩
        change RateLE l T (fun _=>(1:ℂ)) (u * wages v () - ((fun c=>weightOf c) v)*u)
        unfold weightOf weight
        change RateLE l T _ (u*wages v () - (∑ j:Unit,wages v j)*u); rw [Fintype.sum_unique,mul_comm,sub_self]; exact RateLE.const _ hT
    exact ⟨ ⟨u,le_rfl,fun b hb=> ⟨h.earns hb,fun W r=>⟨(Menu.raw z v),h,Agrees.self U⟩⟩⟩⟩

lemma tariff (t:Tree) (u:ℝ)(a:t.Inner→ℝ)(z:Envelope L t)(v:t.Leaf→S.Tag)(hg:Regular l T t u a z):
   let k:= V t u a (wages v); Supply U l T z (t.topAge u a) k (Menu.raw z v) ∧ Meets U R l T z (Tree.center z) (t.topAge u a) k (Menu.raw z v) := by
      induction t generalizing u with
      | bud => let ht:=bud_supply U hT h u v z a
               exact ⟨ht,Supply.achieves U R h hT hg.nonneg (hg.extent hT) hg.vanish ht⟩
      | fork n f ih => let h₁(j:Fin n):= ih j (a (Sum.inl ())) _ _ (childWages j v) (hg.inside j)
                       let ht:=supplies U R hT v hg (fun j=>(h₁ j).1) (fun j=>(h₁ j).2)
                       exact ⟨ht,Supply.achieves U R h hT hg.nonneg (hg.extent hT) hg.vanish ht⟩
end Assembly
end YM.OPE.Nesting.Fusion

import YM.Contacts.Transport.Recall
/-!
# Arity transport on canonical overlapping products

Naturality required before taking any integration; covers change of order or slicing in ambient
variables independently of the linear reader. Works also on arity zero (empty stages).
-/
set_option autoImplicit false
set_option maxHeartbeats 600000
noncomputable section
namespace YM.Contacts.Transport
open Function Set Normal Submodule Ordered MultipleContact
open scoped Topology Classical BigOperators ContDiff TensorProduct InnerProductSpace
variable {E F A B : Type}[NormedAddCommGroup E][InnerProductSpace ℝ E][FiniteDimensional ℝ E]
  [NormedAddCommGroup F][InnerProductSpace ℝ F][FiniteDimensional ℝ F]
 [CommRing A][Algebra ℂ A][CommRing B][Algebra ℂ B]
variable {k n : ℕ}{U:E→ₗᵢ[ℝ] F}{P : E→ₗᵢ[ℝ] Points k}{T : F→ₗᵢ[ℝ] Points n}
 {f g : Normal.Group k}{t:Fin k↪ Fin n}{o:Points k}{o' : Points n}{c:F}{s : Ortho}{w : E4}
variable (R : Ribbon t P T U c o o' s w g)
variable {b : Bool}{Y : System E A k}{Z : System F B n}{σ:A→+* B}

/-- Data only on the columns of this root, including after permutation or padding. -/
structure Joint (t:Fin k↪ Fin n)(b : Bool)(σ : A→+* B)(v:E→F)(g : Normal.Group k)(Y : System E A k)(Z : System F B n) : Prop where
  active i (h:i∈g) : Z.deg (t i)=Y.deg i -- replace Cyrillic a
  fields i (h:i∈g) x : Z.field (t i) (v x)= σ (Y.field i x)
  readers (f : Normal.Group k) (h:f⊆g)(hg:f.Nonempty) (d:ℕ) (x:E)(e:A): σ (Y.reader f d x e) = Z.reader (current t f) d (v x) (σ e)
namespace Joint
local notation "L'" => fun (x:E)=> U x+c
variable (S:Joint t b σ (fun x=> U x+c) g Y Z)
include S
omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F]
lemma smaller (h : f⊆g) : Joint t b σ L' f Y Z:= by constructor; exacts [fun i hi=> S.active _ (h hi),fun i hi=> S.fields _ (h hi),fun f' h'=>S.readers _ (Finset.Subset.trans h' h)]
lemma depth : Z.depth (current t g)=Y.depth g:= by unfold System.depth System.degree System.relative; rw [carries, Finset.card_map,Finset.sum_map,(Finset.sum_congr rfl (fun i hi=> S.active _ hi))]
end Joint
namespace Ribbon
local notation "L'" => fun (x:E)=> U x+c
local notation "V" => current t g
variable (S:Joint t b σ (fun x=> U x+c) g Y Z) (a:ℝ)
include R S
omit R S in
/-- punctual step without requiring hypothesis of estimates upon reindexing. -/
private lemma receding_flow (h : g.Nonempty) (he : ∀ p ⊂ g, p.Nonempty → Recall b L' σ (Y.cumulant P a p) (Z.cumulant T a (current t p))): Recall b L' σ (Y.punctured P a g) (Z.punctured T a V):= by
    let X:Finset (Pieces g):= Finset.univ.erase ⊤; let K:Finset (Pieces V):= Finset.univ.erase ⊤; let e:= (carryParts t g); have hK: K = X.map e.toEmbedding:= by
       ext i; constructor; intro hi; obtain ⟨i,rfl⟩:= e.surjective i; exact Finset.mem_map_of_mem _ (show i∈X from Finset.mem_erase.mpr ⟨(crown t h i).mp ((Finset.mem_erase.mp hi).1), Finset.mem_univ i⟩)
       intro hi; obtain ⟨p,hp,rfl⟩:= Finset.mem_map.mp hi; exact Finset.mem_erase.mpr ⟨(crown t h p).mpr ((Finset.mem_erase.mp hp).1), Finset.mem_univ _⟩
    unfold System.punctured Normal.receding; unfold K at hK; rw [hK]; rw [Finset.sum_map]; apply Recall.sum; intro i hi; change Recall _ _ _ (product i.parts (Y.cumulant P a)) (product (flow t g i).parts (Z.cumulant T a)); rw [flown]; exact Recall.synopsis ( (current t)) _ (fun j hj=> he j (inner_piece i (Finset.mem_erase.mp hi).1 hj) (i.nonempty_of_mem_parts hj)) ((Y.compatible P a).stands i) ((Z.compatible T a).stands (flow t g i))

lemma origin_flow (h : g.Nonempty) : Recall b L' σ (Y.cumulant P a g) (Z.cumulant T a V):= by
    induction g using Finset.strongInductionOn with
    | _ g ih=>
      have hu:(current t g).card = g.card:=Finset.card_map _
      by_cases he : 1<g.card
      · let p:= Y.punctured P a g; let q:=Z.punctured T a (current t g);
        have hp:= receding_flow (P:=P) (T:=T) (b:=b) (σ:=σ) (U:=U) (t:=t) (Y:=Y) (Z:=Z) a h (fun p hp hq=> ih p hp (R.smaller hp.le) (S.smaller hp.le) hq); rw [Y.equation_subtract P a _ he,Z.equation_subtract T a _ (hu.symm ▸ he)];
        unfold System.subtractAt; apply Recall.negation; -- after? subtractAt def behind Recall expected; reorder
        change Recall b _ σ (∑ w:Fin (Y.depth g),reshape (Y.reader g w) p * instructionScore E A (taylor (normalOn P g) a (Y.depth g -1-w.val))) _; rw [S.depth]; refine Recall.sum _ fun w _=> Recall.multiply (Recall.column hp (?_)) (Recall.illumination _ _ (taylor_both R _ _ h b)); exact fun x e=> S.readers g (by rfl) h w x e
      obtain ⟨i,rfl⟩:= Finset.card_eq_one.mp (show g.card=1 from le_antisymm (not_lt.mp he) h.card_pos); rw [Y.single_op, carries,Finset.map_singleton,Z.single_op]; exact Recall.atom (S.fields i (Finset.mem_singleton_self i)) (fun x y h=> h)
lemma punt_flow (h : g.Nonempty) : Recall b L' σ (Y.punctured P a g) (Z.punctured T a V):= receding_flow (P:=P) (T:=T) (b:=b) (σ:=σ) (U:=U) (t:=t) (Y:=Y) (Z:=Z) a h (fun _ hi hh=> (R.smaller hi.le).origin_flow (S.smaller hi.le) a hh)
lemma full_flow (h : g.Nonempty) : Recall b L' σ (Y.full P a g) (Z.full T a V):= by rw [Y.full_formula P a g h,Z.full_formula T a V h.map]; exact (R.punt_flow S a h).plus (R.origin_flow S a h)
lemma bank_flow (K : Pieces g) : Recall b L' σ (parcel (Y.full P a) K) (parcel (Z.full T a) (flow t g K)):= by unfold parcel; rw [flown]; exact Recall.synopsis (current t) _ (fun i hi=> (R.smaller (K.le hi)).full_flow (S.smaller (K.le hi)) a (K.nonempty_of_mem_parts hi)) ((Y.can_use P a).stands K) ((Z.can_use T a).stands (flow t g K))
end Ribbon
end YM.Contacts.Transport

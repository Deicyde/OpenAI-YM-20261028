import YM.MultipleContact.Panel.PairTest
/-! Independence of the order of performing independent Taylor operations in a joint test. -/
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section
namespace YM.MultipleContact.Panel
open Set Function Filter MeasureTheory Table Extraction Ward Metric TopologicalSpace
open scoped ContDiff Classical BigOperators MeasureTheory Distributions Topology
variable {X V W:Type*}[NormedAddCommGroup X][NormedSpace ℝ X][NormedAddCommGroup V][NormedAddCommGroup W][InnerProductSpace ℝ V][InnerProductSpace ℝ W](p:Lens X V)(q:Lens X W)
omit p q [NormedAddCommGroup V] [InnerProductSpace ℝ V][NormedAddCommGroup W] [InnerProductSpace ℝ W] in
lemma blades_exchange (A B:List X)(f:X→ℂ)(hf:ContDiff ℝ ∞ f):blades A (blades B f)= blades B (blades A f):=by
       induction A with
       |nil=> rfl
       |cons u t IH=> change blade u (blades t (blades B f))= blades B (blade u (blades t f)); rw [IH]; exact blades_pin (blades_smooth hf t) B u

def blind:= (∀y,p.read (q.put y)=0) ∧ ∀y,q.read (p.put y)=0
lemma blind.symm (h:blind p q):blind q p:=⟨h.2,h.1⟩
lemma blind.tail (h:blind p q)(x:X):p.read (q.off x)=p.read x:=by change p.read (x-q.put (q.read x))=_;rw [map_sub,h.1,sub_zero]
lemma blind.off (h:blind p q)(x:X):p.off (q.off x)=q.off (p.off x):=by change q.off x-p.put (p.read (q.off x))=p.off x-q.put (q.read (p.off x)); rw [h.tail,h.symm.tail]; change x-q.put (q.read x) - p.put (p.read x)= x - p.put (p.read x) -q.put (q.read x); abel
private def array(p:Lens X V)(i:ℕ)(x:X):List X:=List.ofFn (fun _:Fin i=>p.put (p.read x))
private def jointAtom(i j:ℕ)(f:X→ℂ)(x:X):ℂ:= (i.factorial:ℝ)⁻¹ • (j.factorial:ℝ)⁻¹ • blades (array p i x) (blades (array q j x) f) (p.off (q.off x))
private lemma mixed (h:blind p q)(i j:ℕ)(f:X→ℂ)(hf:ContDiff ℝ ∞ f)(x:X):jointAtom p q i j f x=jointAtom q p j i f x:= by unfold jointAtom; rw [blades_exchange _ _ f hf,h.off,smul_comm]; -- maybe rw loops
variable {p q}
lemma blind.shrinks_atom (h:blind p q)(i m:ℕ){f:X→ℂ} (hf:ContDiff ℝ ∞ f)(x:X)(b:ℝ):p.atom i (q.trim b m f) x=p.atom i f x - cutoff b (q.read x) • ∑j∈Finset.range (m+1), jointAtom q p j i f x:=by
          let t:=q.trim b m
          have he:blades (array p i x) (q.trim b m f)=q.trim b m (blades (array p i x) f):=q.blades_trim (array p i x) (by intro v hv; obtain ⟨u,rfl⟩:=List.mem_ofFn.mp hv; exact h.2 _) f hf m b
          rw [p.atom_blades i _ x (q.trim_smooth m b hf),p.atom_blades i f x hf]
          dsimp only [array] at he; rw [he]
          rw [Lens.trim,h.symm.tail,smul_sub]; congr 1
          rw [smul_comm,Finset.smul_sum,Lens.atoms,Finset.smul_sum,Finset.smul_sum]; apply Finset.sum_congr rfl; intro j hj
          apply congr_arg
          unfold jointAtom
          rw [q.atom_blades j _ (p.off x) (blades_smooth hf _),h.symm.tail,smul_comm (i.factorial:ℝ)⁻¹ (j.factorial:ℝ)⁻¹]; rfl -- solve via smul_comm instead of ← smul_smul
lemma blind.trim_comm (h:blind p q)(n m:ℕ){f:X→ℂ} (hf:ContDiff ℝ ∞ f)(a b:ℝ):p.trim a n (q.trim b m f)=q.trim b m (p.trim a n f):=by
          funext x
          change q.trim b m f x - cutoff a (p.read x) • p.atoms n (q.trim b m f) x = p.trim a n f x - cutoff b (q.read x) • q.atoms m (p.trim a n f) x
          unfold Lens.atoms
          -- unfold inner atoms may prematurely reduce trim there; avoid indiscriminate
          simp_rw [h.shrinks_atom _ _ hf x b,h.symm.shrinks_atom _ _ hf x a, mixed q p h.symm _ _ f hf]
          unfold Lens.trim Lens.atoms
          rw [Finset.sum_sub_distrib,Finset.sum_sub_distrib,← Finset.smul_sum,← Finset.smul_sum,smul_sub,smul_sub]
          rw [Finset.sum_comm (s:=Finset.range (m+1)),smul_comm (cutoff b _) (cutoff a _)]; abel

lemma port_permute {b k:ℕ}{a a':List (Fin b×ℕ)} (ha:List.Perm a a')(ha':(a.map Prod.fst).Nodup) (s:ℝ){f:PairSet.Board b k→ℂ} (hf:ContDiff ℝ ∞ f):Factors (PairSet.port k) s a f=Factors (PairSet.port k) s a' f:=by
          let T:List (Fin b×ℕ) → (PairSet.Board b k→ℂ)→ PairSet.Board b k→ℂ:=Factors (ι:=Fin b) (PairSet.port (b:=b) k) s; change T a f=T a' f
          induction ha with
          | nil=>rfl
          | cons x h IH=> simp only [T,Factors]; change (PairSet.port k x.1).trim s _ (T _ f) = (PairSet.port k x.1).trim s _ (T _ f); rw [IH (List.nodup_cons.mp ha').2]
          | swap x y l=>
             have h0: x.1 ≠ y.1:= by rintro e; exact (List.nodup_cons.mp ha').1 (List.mem_cons.mpr (Or.inl e.symm)) -- ha' left Which swap constructor? inspect
             exact blind.trim_comm (show blind (PairSet.port k _) (PairSet.port k _) from ⟨fun i=>PairSet.port_cross k y.1 x.1 (Ne.symm h0) _,fun i=>PairSet.port_cross _ _ _ h0 _⟩) y.2 x.2 (Factors_smooth _ s l hf) s s
          | trans h h' IH IH'=> exact (IH ha').trans (IH' (List.Perm.nodup (List.Perm.map _ h) ha'))
end YM.MultipleContact.Panel

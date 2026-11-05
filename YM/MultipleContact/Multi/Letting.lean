import YM.MultipleContact.Multi.Signs
import YM.Extraction.Around
import YM.Cells.Transforms
import YM.Next.UV_STRESS.Tiles
/-! Convergence of signed polynomial templates entirely on genuine common grid arrays (with changing label coefficients). -/
set_option autoImplicit false
set_option maxHeartbeats 2400000
noncomputable section
namespace YM.MultipleContact.Flight
open Function Filter MeasureTheory Lattice Wilson RG Extraction Table Spec Cells Script Ward Set
open scoped Topology BigOperators InnerProductSpace ContDiff Classical
variable {G:Gauge}{C:Family G}{L:Register G}(F:Extraction.Order){S:Table C.book}{n m d:ℕ}
variable {P α:Type*} {w:Fin n → Cover} {t:ℕ}
def prodM {P X:Type*}[CommMonoid X](f:P→X):Multiplicative (Multiset P)→*X where
   toFun m:= (m.toAdd.map f).prod
   map_one' := by change (Multiset.map f 0).prod=1; simp
   map_mul' m n:= by simp [Multiset.map_add]
def assign (f:P→ℂ) : Grammar P→ₐ[ℂ]ℂ:= AddMonoidAlgebra.lift ℂ ℂ (Multiset P) (prodM f)
lemma assign_spell {ι:Type*}[Fintype ι](x:ι→P)(f:P→ℂ): assign f (spell x)=∏i,f (x i):=by
       unfold spell stamp;rw [map_prod]; exact Finset.prod_congr rfl fun i hi=> (by rw [assign,AddMonoidAlgebra.lift_single]; simp [prodM])
variable (H:S.Hierarchy)(hp:F.PointLimits C S)
variable {q: Filter (ℕ×ℕ)} (hq:q ≤ F.fuse)
include H hp hq
private lemma lim_numeric_labels {D:Fin n→ℕ} (v:ℕ×ℕ→∀i:Fin n, C.book.Ref (D i)) -- replace
   (vL:Π i, C.book.Ref (D i)) (hv:Tendsto v q (𝓝 vL))(hz:Order.grid C t w∈generic n):
   Tendsto (fun i:ℕ×ℕ=> C.numeric i.1 i.2 (fun j:Fin n=>(⟨D j,v i j⟩:C.book.Token)) (location C.S t i.1 i.2 ∘ w)) q (𝓝 (Ward.disc (fun j:Fin n=>⟨D j,S.project _ (vL j)⟩) (Order.grid C t w))):=by
      let U (i:Fin n):= C.book.Ref (D i); let b i : Module.Basis (Fin (Module.finrank ℂ (U i))) ℂ (U i):=Module.finBasis ..
      let z:=Order.grid C t w
      have hT(i:ℕ×ℕ) (a:Π j, C.book.Ref (D j)): C.numeric i.1 i.2 (fun j:Fin n=>(⟨D j,a j⟩:C.book.Token)) (location C.S t i.1 i.2∘ w)=∑ k:(Π p,Fin (Module.finrank ℂ (U p))), (∏ j, (b j).repr (a j) (k j)) • C.numeric i.1 i.2 (fun j=>(⟨D j,b j (k j)⟩:C.book.Token)) (location C.S t i.1 i.2∘w):= by exact basis_express (C.ensemble D (location C.S t i.1 i.2∘w)) b _
      have hS':disc (fun i:Fin n=> ⟨D i,S.project (D i) (vL i)⟩) z=S.value D z vL:=by
           exact S.at_project _ H.laws.toSymmetric (fun _=>le_refl _) (generic_conf _ hz) (fun i:Fin n=>⟨D i,vL i⟩)
      change Tendsto _ _ (𝓝 (disc _ z)); rw [hS',basis_express (S.value D z) b vL]; conv => arg 1; ext i; rw [hT i (v i)]
      refine tendsto_finsetSum _ (fun k _=> ?_)
      have hg(j:Fin n):Tendsto (fun i=> ((b j).repr (v i j)) (k j):ℕ×ℕ →ℂ) q (𝓝 (((b j).repr (vL j)) (k j))) := ( ((b j).coord (k j)).continuous_of_finiteDimensional.comp (continuous_apply (A:=fun i=> C.book.Ref (D i)) j)).continuousAt.tendsto.comp hv
      exact Tendsto.smul (tendsto_finsetProd _ fun j _=> hg j ) ((Order.along (Cells.eventual_grid C F S hp w hz (fun j:Fin n=> ⟨D j,b j (k j)⟩:Fin _→ C.book.Token))).mono_left hq)

def report (C:Family G) (x:Grammar P)(z:P → Cover)(t:ℕ)(v:P→ C.book.Token) (i:ℕ×ℕ):=moment (C.beta i.1 i.2) (fun U:Config G (C.side i.1 i.2)=>assign (P:=P) (fun p=>C.seen (v p) (location C.S t i.1 i.2 (z p)) U) x)
variable {C0:Family G}{L':Register G}
def render (T:Table L') (x:Grammar P)(z:P→ E4)(u:P→T.Tag) := evaluation T (Script.rewrite (fun p:P=>(u p,z p)) x)
private def MonRead (C:Family G)(x:P → Cover)(t:ℕ)(D:P→ℕ)(v:P→ C.book.Token)(i:ℕ×ℕ)(m:Multiset P):=
       let w:= (letters_frame m).choose
       C.numeric i.1 i.2 (fun q=>v (w q)) (Cells.location C.S t i.1 i.2 ∘ (x∘w))
omit H hp hq in
lemma report_exp (x:Grammar P) (z:P → Cover)(t:ℕ)(D:P→ℕ)(v:P→ C.book.Token)(i:ℕ×ℕ):report C x z t v i=∑ m∈x.coeff.support, x.coeff m * MonRead C z t D v i m:=by
     conv_lhs => unfold report; rw [sum_terms x]; simp only [map_sum,map_smul]
     unfold Wilson.moment; rw [integral_finsetSum]
     · exact Finset.sum_congr rfl fun m hm=>by simp_rw [assign_spell,smul_eq_mul]; rw [show (∫ u, _ ∂_) = x.coeff m * (∫ u, _ ∂_) from integral_const_mul _ _]; rw [MonRead,C.num]; rfl
     intro m hm; simp_rw [assign_spell]; exact continuous_integrable (C.beta i.1 i.2) ((continuous_finsetProd _ (fun j h=> (C.continuousO i.1 i.2 (v ((letters_frame m).choose j)).1 ..))).const_smul (x.coeff m))

omit H hp hq
def Admissible [DecidableEq P] {A:Type*}(z:P → A)(K:Set A)(x:Grammar P):Prop:= ∀ m∈ x.coeff.support,(m.map z).Nodup ∧ ∀ i∈m,z i∈K
variable {r A:Type*}[DecidableEq P]
variable {p p':Grammar P} {Z:P→ A} {K T:Set A}
lemma admissible_spell {ι:Type*}[Fintype ι](v:ι→P) (ht:Injective (Z ∘ v))(hr:∀i,Z (v i)∈K):Admissible Z K (spell v):=by
    classical
    intro m hm; rw [Script.spell_eq] at hm
    simp only [AddMonoidAlgebra.coeff_single,Finsupp.support_single_ne_zero _ one_ne_zero,Finset.mem_singleton] at hm
    rw [hm,letters_eq, Multiset.map_map]
    exact ⟨Finset.nodup (Finset.univ:Finset ι) |>.map ht,fun i h=>by obtain ⟨i,_,rfl⟩:=Multiset.mem_map.mp h; exact hr _⟩
lemma Admissible.weak (h:K⊆T)(hp:Admissible Z K p):Admissible Z T p:=fun i hi=>⟨(hp i hi).1,fun r hr=>h ((hp i hi).2 r hr)⟩
lemma admissible_one : Admissible Z K 1:=by intro m hm; rw [AddMonoidAlgebra.one_def] at hm; simp only [AddMonoidAlgebra.coeff_single,Finsupp.support_single_ne_zero _ one_ne_zero,Finset.mem_singleton] at hm; rcases hm with rfl; simp
lemma Admissible.add (h:Admissible Z K p)(h':Admissible Z K p'):Admissible Z K (p+p'):=by intro m hm; obtain ht|ht := Finset.mem_union.mp (Finsupp.support_add (show m∈(p.coeff+p'.coeff).support from hm)); exacts [h _ ht,h' _ ht]
lemma Admissible.scalar (h:Admissible Z K p)(c:ℂ):Admissible Z K (c • p):=by intro m hm; exact h _ (Finsupp.support_smul (show m∈ (c • (p.coeff)).support from hm))
lemma Admissible.diff (h:Admissible Z K p)(h':Admissible Z K p'):Admissible Z K (p-p'):=(show p+(-1:ℂ)•p'=p-p' by rw [neg_one_smul]; simp only [sub_eq_add_neg]) ▸ Admissible.add h (Admissible.scalar h' _)
lemma Admissible.join (h:Admissible Z K p) (h':Admissible Z T p')(hf:Disjoint K T):Admissible Z (K∪T) (p*p'):=by
    intro m hm; obtain ⟨k,hk,l,hl,rfl⟩:=Finset.mem_image₂.mp (AddMonoidAlgebra.support_coeff_mul_subset p p' hm)
    obtain ⟨he,hh⟩:=h k hk; obtain ⟨he',hh'⟩:=h' l hl
    refine ⟨?_ ,?_⟩
    · rw [Multiset.map_add,Multiset.nodup_add]; apply And.intro he; refine ⟨he',Multiset.disjoint_left.mpr (fun {r} hr hr'=>?_ )⟩; obtain ⟨i,hi,hI⟩:=Multiset.mem_map.mp hr; obtain ⟨i',hi',hI'⟩:=Multiset.mem_map.mp hr'; exact Set.disjoint_left.mp hf (hI ▸ hh _ hi) (hI' ▸ hh' _ hi')
    intro r hr; obtain hw|hw:=Multiset.mem_add.mp hr
    · exact Or.inl (hh r hw)
    exact Or.inr (hh' r hw)
lemma admissible_prod {α:Type*}{Q:Finset α}{P':α→Set A}{x:α→Grammar P}(hP:∀i∈Q,Admissible Z (P' i) (x i))(hd:(↑Q:Set α).Pairwise (fun i j=>Disjoint (P' i) (P' j))):
    Admissible Z (⋃ i∈Q,P' i) (Q.prod x):=by
    classical
    induction Q using Finset.induction with
    | empty=> rw [Finset.prod_empty]; exact admissible_one
    | @insert i q hi ih =>
      rw [Finset.prod_insert hi]; apply Admissible.weak ?_ (Admissible.join (hP i (Finset.mem_insert_self ..)) (ih (fun _ h=>hP _ (Finset.mem_insert_of_mem h)) (hd.mono (by simp))) ?_)
      · intro r hr; obtain he|he:=hr
        · exact Set.mem_iUnion₂.mpr ⟨_,Finset.mem_insert_self ..,he⟩
        obtain ⟨j,hj,hh⟩:=Set.mem_iUnion₂.mp he; exact Set.mem_iUnion₂.mpr ⟨j,Finset.mem_insert_of_mem hj,hh⟩
      rw [Set.disjoint_left]; intro r hr hs; obtain ⟨j,hj,he⟩:=Set.mem_iUnion₂.mp hs
      exact (Set.disjoint_left.mp (hd (Finset.mem_insert_self i q) (Finset.mem_insert_of_mem hj) (by aesop))) hr he
lemma Admissible.pick (h:Admissible Z K p){m:Multiset P}(hm:m∈p.coeff.support):
    Injective (Z ∘ (letters_frame m).choose):=by
        have he := (h _ hm).1
        rw [(letters_frame m).choose_spec] at he -- same m in choose_spec, rw rewrites m there? rw at target only
        rw [letters_eq, Multiset.map_map,Multiset.nodup_map_iff_inj_on Finset.univ.nodup] at he
        exact fun i j h=>he i (Finset.mem_val.mpr (Finset.mem_univ _)) j (Finset.mem_val.mpr (Finset.mem_univ _)) h

def prevent (x:Grammar P)(z:P → E4):Prop:= ∀a:Axis,Admissible (fun i=>z i a) Set.univ x
private def evalWord (T:Table L)(z:P → E4)(v:P→T.Tag)(m:Multiset P):ℂ:=readFin T (fun i=> ((v (((letters_frame m).choose) i)),(z (((letters_frame m).choose) i))))
lemma render_exp [DecidableEq P](T:Table L)(x:Grammar P)(z:P → E4)(v:P→T.Tag)(hp:T.Hierarchy): render T x z v=∑ m∈ x.coeff.support, x.coeff m * evalWord T z v m:=by
      conv_lhs=>unfold render; rw [sum_terms x]; simp only [map_sum,map_smul,rewrite_spell]
      exact Finset.sum_congr rfl fun m hm=> congr_arg (x.coeff m • ·) (eval_fin T hp.laws.toSymmetric _)
include H hq hp in
lemma through (x:Grammar P)(z:P → Cover)(t:ℕ)(D:P→ℕ)(v:∀ p:P, (ℕ×ℕ → C.book.Ref (D p)))(vL:Π p:P, C.book.Ref (D p)) (hv:∀p,Tendsto (v p) q (𝓝 (vL p))) (hT:prevent x (fun p=>C.S.gridPoint t (z p))): Tendsto (fun i:ℕ×ℕ=> report C x z t (fun p:P=>⟨D p,v p i⟩) i) q (𝓝 (render S x (fun p=>C.S.gridPoint t (z p)) (fun p=>⟨_,S.project _ (vL p)⟩))):=by
    classical
    let z':=fun i=> C.S.gridPoint t (z i); let v':=fun i p=> (⟨D p,v p i⟩:C.book.Token); let w i := S.classTokens (⟨_,vL i⟩:C.book.Token)
    have h m (ht : m∈x.coeff.support):
       let X := (letters_frame m).choose
       Tendsto (fun i=> MonRead C z t D (v' i) i m) q (𝓝 (evalWord S z' w m)):=by
           intro X
           have hz : Extraction.Order.grid C t (z∘X) ∈ generic _:=(fun a i j he=> (hT a).pick ht he)
           have h' : clear S ((fun i:P=>(w i,z' i)) ∘ X):= (generic_conf ..) hz
           rw [evalWord,readFin,if_pos (show (clear S fun i => (((w (((letters_frame m).choose) i)),(z' (((letters_frame m).choose) i))))) from h')]; exact lim_numeric_labels F (t:=t) H hp hq _ _ (tendsto_pi_nhds.mpr fun i=> (hv (X i))) hz
    change Tendsto (fun i=>report C x z t (v' i) i) q (𝓝 (render S x z' w))
    rw [render_exp S _ _ _ H]; simp_rw [report_exp x z t D (v' _)]; exact tendsto_finsetSum _ (fun m hi=>(h _ hi).const_mul (x.coeff m))

lemma render_cont {L':Register G}(T:Table L') (hp:T.Hierarchy) (x:Grammar P)[DecidableEq P](v:P→T.Tag) (z:P→ E4)(hz:Admissible z univ x): ContinuousAt (fun w:P → E4=>render T x w v) z:=by
     unfold ContinuousAt; dsimp only []
     unfold render
     rw [sum_terms x]; simp only [map_sum,map_smul,rewrite_spell]
     apply tendsto_finsetSum -- replace
     intro m hm; let X:= (letters_frame m).choose
     have hx : Injective (fun i=> z (X i)) := hz.pick hm
     exact ContinuousAt.const_smul (placed_continuous T hp (fun i u=>u (X i)) (fun i=> (continuous_apply (A:=fun _=>E4) (X i)).continuousAt) (v:=fun i (_:P → E4)=> (v (X i)).2) (fun i=> continuousAt_const) hx) (x.coeff m)
end YM.MultipleContact.Flight

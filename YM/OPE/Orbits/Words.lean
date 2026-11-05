import YM.OPE.Single
import YM.Work.A15

/-! Separated words on the true complexified physical filtration.
All truncations/projections below will be on `S.Field` (the actual
quotient), not on bare polynomial coordinates. `moment` follows `Table`'s
convention of specifying something even off Conf; it is used physically
only **on** Conf. -/
set_option autoImplicit false
noncomputable section
namespace YM.OPE.Orbits
open Function Set Filter MeasureTheory Extraction Table Word
open scoped Topology BigOperators ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{L:Register G}{S T:Table L}{I J : Type}[Fintype I][Fintype J]{d:I→ℕ}

abbrev Labels (S:Table L)(d:I→ℕ):= ∀ i:I,S.Field (d i)
def names (v:Labels S d)(i:I):L.Token:= Sigma.mk _ (S.representative _ (v i))
def tags (v:Labels S d)(i:I):S.Tag:= ⟨d i,v i⟩
def quoteTag (a:S.Tag) : L.Token := ⟨a.fst,S.representative _ a.snd⟩

/-- Named quotient-field moment, via its multilinear map. -/
def moment {S:Table L}(T:Table L){d:I→ℕ}(x:I→ E4) :
    MultilinearMap ℂ (fun i=> S.Field (d i)) ℂ where
  toFun v := S.useAt T (points (x ∘ runNames I)) (fun i=> tags v (runNames I i))
  map_update_add' v i a b := by
    classical
    let f := S.classMoment T (d ∘ runNames I) (points (x ∘ runNames I))
    change f (fun k=> update v i (a+b) (runNames I k))=
          f (fun k=> update v i a (runNames I k)) + f (fun k=> update v i b (runNames I k))
    obtain ⟨i,rfl⟩:= (runNames I).surjective i
    have hv (s:S.Field (d (runNames I i))): (fun k=> update v (runNames I i) s (runNames I k)) = update (β:=fun k => S.Field (d (runNames I k))) (fun k=>v (runNames I k)) i s:=by
       funext k; by_cases he:k=i; · subst k; rw [update_self, update_self]
       rw [update_of_ne he,update_of_ne ((runNames I).injective.ne he)]
    rw [hv (a+b),hv a,hv b]; exact f.map_update_add ..
  map_update_smul' v i c a := by
    classical
    let f:= S.classMoment T (d ∘ runNames I) (points (x ∘ runNames I))
    change f (fun k=> update v i (c • a) (runNames I k)) = c • f (fun k=> update v i a (runNames I k))
    obtain ⟨i,rfl⟩:= (runNames I).surjective i
    have hv (s:S.Field (d (runNames I i))): (fun k=> update v (runNames I i) s (runNames I k)) = update (β:=fun k => S.Field (d (runNames I k))) (fun k=>v (runNames I k)) i s:=by
       funext k; by_cases he:k=i; · subst k; rw [update_self, update_self]
       rw [update_of_ne he,update_of_ne ((runNames I).injective.ne he)]
    rw [hv (c•a),hv a]; exact f.map_update_smul ..

lemma observed {e:I→ℕ}(a:Labels S e)(x:I→E4): moment T x a=observe T x (names a):=by
    unfold observe worded; rw [T.readAt]; rfl

variable {a:Labels S d}{y:I→E4}
lemma carrying (hT:T.Hierarchy) (hy:Injective y)(s:E4) : moment T (fun i=> y i + s) a = moment T y a := by
    rw [observed,observed]; exact observe_carry T hT.translations _ hy s

lemma permuted (hT:T.Hierarchy) (hy:Injective y)(e:J≃I): moment T (y ∘ e) (fun j=> (a (e j) : S.Field (d (e j))))= moment T y a :=by
    rw [observed,observed]; exact OPE.perm_observe T hT.laws.toSymmetric e (names a) hy

def bar (ρ:S.RealSpin): Labels S d →ₛₗ[starRingEnd ℂ] Labels S d where
    toFun v i := S.conj ρ _ (v i)
    map_add' x y := funext fun _ => map_add ..
    map_smul' c x:= funext fun i => (by
      change S.conj _ _ (c • x i)= (starRingEnd ℂ) c • S.conj _ _ (x i)
      exact map_smulₛₗ ..)
omit [Fintype I] in
@[simp]
lemma bar_bar (ρ:S.RealSpin) : bar ρ (bar ρ a)=a:= funext fun _=> Table.reflect_star S ρ _ _

lemma bar_observes (ρ:S.RealSpin) (hT:T.Hierarchy) (hS:T.respects S)(hy:Injective y) : moment T y (bar ρ a)=star (moment T y a):=by
    rw [observed,observed]; unfold observe worded; rw [T.readAt,T.readAt]
    have hi: S.useAt T (points (y ∘ runNames I)) (fun i=> S.classTokens ((names (bar ρ a) ∘ runNames I) i)) = S.useAt T (points (y ∘ runNames I)) (S.classTokens ∘ L.conjugate ∘ names a ∘ runNames I):=by
       congr 1; funext i
       change (S.classTokens (names (bar ρ a) (runNames I i))) = S.classTokens (L.conjugate (names a (runNames I i)))
       change (⟨_,S.project _ (S.representative _ _)⟩:S.Tag) = ⟨_,S.project _ (star (S.representative _ _))⟩
       simp only [names,Register.conjugate] -- Register.conjugate syntax fix
       erw [S.rep,← S.conj_project ρ, S.rep]; rfl
    exact (S.at_project T hT.laws.toSymmetric hS (runs_conf.mpr hy) _).symm.trans (hi.trans ((S.at_project T hT.laws.toSymmetric hS (runs_conf.mpr hy) _).trans (hT.spin.real (runs_conf.mpr hy) _)))

def roll (V:S.Rotation) (k:Ortho): Labels S d ≃ₗ[ℂ] Labels S d:= LinearEquiv.piCongrRight fun i=> V.act (d i) k

lemma roll_observes (V:S.Rotation)(k:Ortho)(hT:V.Oriented T)(hy:Injective y) :
    moment T (Ortho.move k ∘ y) (roll V k a) = moment T y a := by
    apply hT _ (fun i=> (⟨d (runNames I i),a (runNames I i)⟩:S.Tag)) _ (runs_conf.mpr hy)

lemma totalized_carry (hT:T.Hierarchy) (y:I→ E4) (s:E4) :
    let z:= fun i=> y i+s
    (if Injective z then moment T z a else 0) = if Injective y then moment T y a else 0 := by
       classical
       intro z
       by_cases hy:Injective y
       · have hh: Injective z:= fun i j h=> hy (add_right_cancel h)
         rw [if_pos hh,if_pos hy,carrying hT hy]
       rw [if_neg hy,if_neg (fun hp=> hy (by intro i j he; exact hp (show z i=z j from congr_arg (·+s) he)))]

section Product
variable {A: I→ Type}{B:J→ Type}{W:Type*} [∀i,AddCommGroup (A i)][∀i,Module ℂ (A i)] [∀j,AddCommGroup (B j)][∀j,Module ℂ (B j)] [AddCommGroup W][Module ℂ W]

def pack (x:∀i,A i)(y:∀j,B j): ∀ q:I⊕J,Sum.elim A B q | .inl i=> x i | .inr j=> y j

def stages (x:Labels S d){f:J→ℕ}(y:Labels S f) : Labels S (Sum.elim d f)
 | .inl i=> x i
 | .inr j=> y j

def sectionLabels {d:I⊕J → ℕ} (y:∀ j:J, S.Field (d (.inr j)))
    (m:MultilinearMap ℂ (fun i=> S.Field (d i)) W) : MultilinearMap ℂ (fun i=> S.Field (d (.inl i))) W:=by
    classical
    let f(x:Labels S fun i=>d (.inl i)) (i:I⊕J):S.Field (d i):= Sum.rec x y i
    refine { toFun x:= m (f x), map_update_add' := ?_, map_update_smul' := ?_ }
    <;> (intro K; have : K = Classical.decEq _:=Subsingleton.elim _ _; subst K; have he(x:Labels S fun i=>d (.inl i)) (i:I) v: f (update x i v)=update (β:=fun j=> S.Field (d j)) (f x) (.inl i) v:=by
            funext j; rcases j with j|j
            · by_cases h:j=i; subst j; · rw [update_self]; exact update_self ..
              rw [update_of_ne (Sum.inl_injective.ne h)]; exact update_of_ne h ..
            rw [update_of_ne Sum.inr_ne_inl])
    · intros; rw [he,m.map_update_add, he,he]
    intros; rw [he,m.map_update_smul,he]

omit [Fintype I] [Fintype J] in
lemma sectionLabels_apply {d:I→ ℕ}{e:J→ℕ} (y:Labels S e)
   (m:MultilinearMap ℂ (fun i=> S.Field (Sum.elim d e i)) W) (x:Labels S d) :
   sectionLabels (d:=Sum.elim d e) y m x = m (stages x y):=by
      change m (fun i=> (Sum.rec x y i : S.Field (Sum.elim d e i)))=_
      congr 1; funext i; cases i <;> rfl
end Product
end YM.OPE.Orbits

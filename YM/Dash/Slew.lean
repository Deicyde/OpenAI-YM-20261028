import YM.Dash.Regular

/-!
# Up through projections, with enough distribution derivatives
-/
set_option autoImplicit false
noncomputable section
namespace YM.Dash
open Set Filter MeasureTheory Measure Complex Analysis Extraction Boundary TopologicalSpace Metric Function
open scoped ContDiff Topology FourierTransform InnerProductSpace BigOperators
variable {G : Gauge} {L : Register G} {n : ℕ}

def Live (S : Table L) := ∀ n (v : Fin n→L.Token), Loc fun x => S.read x v

def old (S : Table L) := ∀ n (v : Fin n → L.Token), ContinuousOn (fun x => S.read x v) (generic n)

def closeBy (K : Table L) := ∀ n (v : Fin n → L.Token) (i : Fin n) (a : Axis),
    ∃ w : Fin n→L.Token,currents (fun x => K.read x v) (fun x => K.read x w) i a

def matchReg (S T : Table L) := ∀ n (v : Fin n→L.Token),EqOn (fun x => T.read x v) (fun x => S.read x v) (generic n)

lemma faithful {S T : Table L} (h : matchReg S T) (t : Test n) (v : Fin n → L.Token) :
    t.applyTo (fun x => S.read x v)=t.applyTo (fun x => T.read x v) := by
  apply integral_congr_ae; filter_upwards [almostGeneric n] with x hx; rw [show T.read x v=S.read x v from h n v hx]

lemma awake (S : Table L) (h : Live S) (he : old S) (hp : closeBy S) : ∃ T, matchReg S T ∧ T.Smooth := by
  classical
  have hh (n m) (p : Fin n) (a : Axis) (v : Fin n → L.Token) : Hidden p a m (fun x => S.read x v) := by
    induction m generalizing v with
    | zero => exact begins _ _ _ (h n v)
    | succ m IH =>
      obtain ⟨w,hw⟩ := hp n v p a; exact arises p a m (h n v) hw (IH w) (IH v)
  choose t hT H using fun n (v : Fin n → L.Token) => aggregate (h n v) (fun m p a => hh n m p a v) (he n v)
  have hg {n} (d : Caps n) (v : L.Vector d) (x) (hx : x∈generic n) : t n (fun i => ⟨d i,v i⟩) x=S.value d x v := H n _ hx
  let M (n) (x : Points n) (d : Caps n) (h : x∈conf n) : Moment L n d :=
    { toFun := fun v => t n (fun i => ⟨d i,v i⟩) x
      map_update_add' := by
        intro _ v i a b
        apply discl (conf_open n) _ _ (hT n (fun j => ⟨d j,update v i (a+b) j⟩)).continuousOn
          (((hT n (fun j => ⟨d j,update v i a j⟩)).continuousOn).add ((hT n (fun j => ⟨d j,update v i b j⟩)).continuousOn))
          ?_ h
        intro y hy
        rw [Pi.add_apply,hg d _ y hy.2,hg d _ y hy.2,hg d _ y hy.2]
        exact (S.value d y).map_update_add v i a b
      map_update_smul' := by
        intro _ v i a b
        let f := (fun y => a • t n (fun j => ⟨d j,update v i b j⟩) y)
        have ht : ContinuousOn f (conf _) := (continuousOn_const (c:=a) (s:=conf n)).smul (hT n (fun j => ⟨d j, update v i b j⟩)|>.continuousOn)
        apply discl (conf_open n) _ _ (hT n _|>.continuousOn) ht ?_ h
        intro y hy; unfold f; rw [hg d _ y hy.2,hg d _ y hy.2]
        exact (S.value d y).map_update_smul v i a b }
  let T : Table L := { value := fun {n} d x => if h : x ∈ conf n then M n x d h else 0 }
  have he n (x : Points n) (d : Caps n) (v) (ht : x∈conf n) : T.value d x v=t n (fun i => ⟨d i,v i⟩) x := by
    change (dite _ _ _ : Moment L n d) v=_; rw [dif_pos ht];rfl
  exact ⟨T,(fun n v x hx => by
    change T.read x v=S.read x v
    rw [Table.read, he n x _ _ (generic_conf _ hx),hg _ _ x hx]; rfl),⟨fun {n} d v => by
    apply (hT n (fun j => ⟨d j,v j⟩)).congr; intro i hi; exact he _ _ _ _ hi⟩⟩
end YM.Dash

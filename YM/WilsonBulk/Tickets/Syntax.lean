import YM.WilsonBulk.Tickets.Burden

/-!
# Gradient from Ward tests at ANY valence. Preserve true offsets under
   repeated estimates on all roots by swapping leg base. No token arity
   hidden; core permits any chosen untouched relative tenor. USED for
   controlling AFFINE NULL: `ortho` identity exact even when taking many
   Newton mixed derivatives in relative coordinates of arbitrary higher legs.
-/
set_option autoImplicit false
noncomputable section
namespace YM.WilsonBulk
namespace Sheet
open Function Filter Equiv Finset Lattice Laurent RG Precision Pert.Bulk Parapet Exterior
open scoped Topology BigOperators Classical ENNReal
open Taylor (lineRead league)
open MvPolynomial (X C eval rename aeval)
variable {α β γ : Type} {σ τ p q : ℝ} {n d k m : ℕ}
variable {G : Gauge} {P V : Text (Cloth G) (n+1)}
-- take shape L1 in specific hue. Annihilation of diagonal symbolic WT strides.

def regionShift (n : ℕ) (a : Axis) := -cage (step a) (n:=n)
def remote (a : Axis) (u : Formula (Keys n)) := outset (regionShift n a) u - u
abbrev journal (P : Text α (n+1)) (i : α) := motif P (0,i)
lemma compass (pu : Public P) (x : Cover) (i : Cloth G) (t : Legs (Cloth G) n) (q : Formula (Keys n)) (y : Cover) :
    HasSum (fun v=> P (hitch (y,i) (put x t v))*lineRead v q) (journal P i t (outset (cage (y-x)) q)) := by
  let z:Slip n:=cage (y-x); let s:=outset z q
  apply (Equiv.addRight z).hasSum_iff.mp; change HasSum _ (motif _ _ _ s)
  unfold motif; rw [roll_draft pu.style 0 y i]; refine (wells_paid pu (y,i) s t).congr_fun (fun w=>?_); change P (hitch (y,i) (put x t (w+z)))*lineRead (w+z) q= _; rw [enclaves (a:=y) x,show w+z-(cage (y-x))=w from add_sub_cancel_right w z]; rw [show lineRead w s=lineRead (w+z) q from outset_read z w q]; rfl
lemma motif_diss (h : Public P) (k : G.ColorIndex) (t : Legs (Cloth G) n) (u : Formula (Keys n)) :
    journal (diss backed P) (coord 0,k) t u=∑ j:Axis, journal P (coord j,k) t (remote j u) := by
  unfold journal
  let f : Axis → Cloth G:=fun a=>(coord a,k); let a:Mark G := (0,f 0)
  have he (i : Axis) := (compass h 0 (f i) t u (-step i)).sub (wells_paid h (0,f i) u t)
  let W (j:Axis) (x:Slip n):=P (hitch (-(step j),f j) (put 0 t x))*lineRead x u-draft P (0,f j) t x*lineRead x u
  have hz (j:Axis) : HasSum (W j) (journal P (f j) t (remote j u)) := by
    unfold remote journal; rw [← motifL_point h,map_sub,motifL_point,motifL_point]; have hp := he j
    change HasSum (W j) _ at hp; rw [sub_zero,show (cage (-step j))=regionShift n j from rfl] at hp; exact hp
  refine HasSum.tsum_eq ?_; apply ((hasSum_sum (fun j _=> hz j)).congr_fun (fun i=> ?_)) -- syntax
  change draft _ a t i * lineRead i u= _; simp only [W,draft,squire,castTail,diss,cameo, backed,hitch_zero,crop_hitch, Pi.sub_apply,margin,selvedge,a,f,↓reduceIte,zero_sub,Finset.sum_apply,sum_sub_distrib,sum_mul,sub_mul]; -- align Axis
  simp_rw [← Equiv.sum_comp axisEquiv]
  simp [← coord_map]

-- extract p when diagonal-shift invariant (e.g. degree tested only on differences!); choose b symbolically along *any* of the n relative positions
lemma remote_law (a : Axis) (i : Fin n) (b : Axis) (q : Formula (Keys n)) (h : outset (regionShift n a) q=q) : remote a (X (i,b)*q)= if a=b then -q else 0 := by
  unfold remote; rw [map_mul,h]; unfold outset; simp only [regionShift,MvPolynomial.aeval_X]; by_cases hh:a=b
  · simp [cage,hh]; ring
  simp [cage,Ne.symm hh,hh]
lemma first_at_peer (d n : ℕ) (hd : d≤ n) {P : Text (Cloth G) (n+1)} (h : TicketNull (d+1) (diss backed P)) (hp : Public P) (u : Formula (Keys n)) (hu : u.totalDegree<d) (ht : ∀ i,outset (regionShift n i) u=u) (v : Cloth G) (t : Legs (Cloth G) n) :
    journal P v t u=0 := by
  rcases v with ⟨v,i⟩; obtain ⟨b,rfl⟩:= axisEquiv.surjective v
  let k : Fin n:=⟨0,by omega⟩; let p : Formula (Keys n):= X (k,b)*u
  have he : journal _ _ _ p=0 := (TicketNull.basic h (0,coord 0,i) t p (lt_of_le_of_lt (MvPolynomial.totalDegree_mul _ _) (by rw [MvPolynomial.totalDegree_X]; omega)))
  rw [motif_diss hp i t p] at he; simp_rw [p,remote_law _ _ b u (ht _),apply_ite (journal P _ t)] at he
  unfold journal at he ⊢; simp_rw [← motifL_point hp,map_neg,map_zero] at he ⊢; simpa using he
end Sheet
end YM.WilsonBulk

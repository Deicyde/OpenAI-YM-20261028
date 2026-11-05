import YM.Next.RANK.Radian.Projection
import YM.PhysicalNext.RANK_COVARIANCE_ATLAS.Atlas


/-!
# Shutters on the real atlas fibers

Actual signs/basepoint wrap link. Identify Bianchi in the two APIs
so that we can preserve it even for data with harmonic curl slots.
-/
set_option autoImplicit false
noncomputable section
namespace YM.PhysicalNext.RankCovariance
open Function Lattice Laurent Bloch Exterior Matrix Precision Next.Free RG FreeResolvent Finset
open Next.Rank Next.Rank.Atlas Next.Rank.Perch Next.Rank.Beamer Next.Rank.CellsInt
open scoped Topology BigOperators

variable {G : Gauge} {n : Side}

/-- Chamber fields read in PAC, positive axes only. -/
def liftPAC (f : Incidence G n → ℝ) : Vec G n 2 := f ∘ toPAC.symm

def nativeChart (f : Incidence G n → ℝ) : Beamer.Horizon G := fun x=> f (wrap n x.1,x.2)

lemma chart_eq {P : Schedule} {k p : ℕ} (f : Chamber G P k p → ℝ) :
    nativeChart f=Radian.wall_chart f := by ext1 x; simp [Radian.wall_chart,nativeChart,body]

private def trip (a b c : Axis) (h : a<b) (he : b<c) : TypeFace 3 := ⟨{a,b,c},by simp [h.ne, he.ne, (h.trans he).ne]⟩
private lemma cube_hits (T : TypeFace 3) : ∃ (a b c : Axis) (h : a<b) (he : b<c), trip a b c h he=T := by
  obtain ⟨a,b,c,hu,hv,hw,hX⟩ := Finset.card_eq_three.mp T.property
  have hs (i j k : Axis) (h : i<j) (he : j<k) (hz : {i,j,k}=({a,b,c}:Finset Axis)) : trip i j k h he=T := Subtype.ext (hz.trans hX.symm)
  rcases lt_or_gt_of_ne hu with h|h
  · rcases lt_or_gt_of_ne hw with he|he; exact ⟨a,b,c,h,he,hs a b c _ _ rfl⟩
    rcases lt_or_gt_of_ne hv with g|g
    · exact ⟨a,c,b,g,he,hs a c b g he (by ext; simp; tauto)⟩
    exact ⟨c,a,b,g,h,hs c a b g h (by ext; simp; tauto)⟩
  rcases lt_or_gt_of_ne hv with he|he
  · exact ⟨b,a,c,h,he,hs b a c h he (by ext; simp; tauto)⟩
  rcases lt_or_gt_of_ne hw with g|g
  · exact ⟨b,c,a,g,he,hs b c a g he (by ext; simp; tauto)⟩
  exact ⟨c,b,a,g,h,hs c b a g h (by ext; simp; tauto)⟩

private lemma d_cube (a b c : Axis) (ha:a<b) (hb:b<c) (v : Body 2 n → ℝ) (x : Site n) :
    let D i j (h:i<j) (k : Axis) := v (x+step k,plaquette ⟨(i,j),h⟩)-v (x,plaquette ⟨(i,j),h⟩)
    (Exterior.d 2 n*ᵥv) (x,trip a b c ha hb)=D b c hb a - D a c (ha.trans hb) b + D a b ha c := by
  intro D; let T := trip a b c ha hb; have hh:=ha.trans hb
  rw [show (Exterior.d 2 n*ᵥv) (x,T)=_ from Exterior.discrete _ _ v _]
  let f (i : Axis) : ℝ:=if h : i∈T.val then parity T.val i ℝ*(v (x+step i,Exterior.remove i T h)-v (x,Exterior.remove i T h)) else 0
  change (∑ i,f i)=_
  have hA : a∈T.val := by simp [T,trip]
  have hB : b∈T.val := by simp [T,trip]
  have hC : c∈T.val := by simp [T,trip]
  have hx : Exterior.remove a T hA=plaquette ⟨(b,c),hb⟩ := by
    ext i; by_cases h : i=a <;> simp [h,Exterior.remove,T,trip,plaquette,ha.ne,hh.ne]
  have hy : Exterior.remove b T hB=plaquette ⟨(a,c),hh⟩ := by
    ext i; by_cases h : i=b <;> simp [h,Exterior.remove,T,trip,plaquette,ha.ne',hb.ne]
  have hz : Exterior.remove c T hC=plaquette ⟨(a,b),ha⟩ := by
    ext i; by_cases h : i=c <;> simp [h,Exterior.remove,T,trip,plaquette,hh.ne',hb.ne']
  have h₁ : parity T.val a ℝ=1 := by simp [parity,T,trip,pre,Finset.filter_insert,Finset.filter_singleton,ha.not_gt,hh.not_gt]
  have h₂ : parity T.val b ℝ= -1 := by simp [parity,T,trip,pre,Finset.filter_insert,Finset.filter_singleton,ha,hb.not_gt]
  have h₃ : parity T.val c ℝ=1 := by simp [parity,T,trip,pre,Finset.filter_insert,Finset.filter_singleton,hb,hh,ha.ne]
  calc
    ∑ i,f i = ∑ i∈T.val,f i := (sum_subset (subset_univ T.val) (fun i _ h=>dif_neg h)).symm
    _ = f a + (f b + f c) := by simp [T,trip,ha.ne,hb.ne,hh.ne]
    _ = _ := by unfold f D; rw [dif_pos hA,dif_pos hB,dif_pos hC,h₁,h₂,h₃,hx,hy,hz]; ring

private def nursery (p : Beamer.Horizon G) (a b c : Axis) :=
  stepValue (polar p b c) a+ stepValue (polar p c a) b+stepValue (polar p a b) c

private lemma sufficient (p : Beamer.Horizon G) (h : ∀ a b c : Axis, a<b → b<c → nursery p a b c=0) : shutter p := by
  have hr (a b c : Axis) : nursery p a b c=nursery p b c a := by unfold nursery; abel
  have hf a i j : stepValue (polar p i j) a= -(stepValue (polar p j i) a) := by
    nth_rw 1 [Beamer.reverse]; ext1 x; simp [stepValue]; abel
  have hb a b c : nursery p a b c = -nursery p b a c := by
    unfold nursery; nth_rw 1 [hf a b c,hf b c a,hf c a b]; abel
  have he (a b : Axis) : nursery p a a b=0 := by
    unfold nursery; nth_rw 1 [hf a a b]; ext1 x; simp [stepValue,polar]
  intro a b c; change nursery _ _ _ _ = _
  rcases lt_trichotomy a b with ht|ht|ht
  · rcases lt_trichotomy b c with hp|hp|hp
    · exact h _ _ _ ht hp
    · subst b; rw [hr]; exact he _ _
    rcases lt_trichotomy a c with hm|hm|hm
    · rw [hb,hr b]; rw [h _ _ _ hm hp,neg_zero]
    · subst a; rw [hr,hr b]; exact he _ _
    rw [hr,hr b]; exact h _ _ _ hm ht
  · subst b; exact he _ _
  rcases lt_trichotomy a c with hp|hp|hp
  · rw [hb,h _ _ _ ht hp,neg_zero]
  · subst a; rw [hr,hr b]; exact he _ _
  rcases lt_trichotomy b c with hm|hm|hm
  · rw [hr]; exact h _ _ _ hm hp
  · subst b; rw [hr]; exact he _ _
  rw [hb,hr b, hr a,h _ _ _ hm ht,neg_zero]

private lemma linked_cube (p : Incidence G n → ℝ) (a b c : Axis) (ha:a<b) (hb:b<c) (i : G.ColorIndex) (x : Cover) :
    nursery (nativeChart p) a b c x i = (tensor G (Exterior.d 2 n)*ᵥliftPAC p) (wrap n x,trip a b c ha hb,i) := by
  let f:=component (liftPAC p) i
  rw [show (tensor G (Exterior.d 2 n)*ᵥliftPAC p) (wrap n x,trip a b c ha hb,i)=(Exterior.d 2 n *ᵥ f) (wrap n x,trip a b c ha hb) from congr_fun (component_mul (Exterior.d 2 n) (liftPAC p) i) (wrap n x,_),d_cube]
  have he (j k : Axis) (h:j<k) (u : Axis) : stepValue (polar (nativeChart p) j k) u x i=f (wrap n x+step u,plaquette ⟨(j,k),h⟩)-f (wrap n x,plaquette ⟨(j,k),h⟩) := by
    let y : PlaqAxes := ⟨(j,k),h⟩
    have hx z : polar (nativeChart p) j k z i=f (wrap n z,plaquette y) := by
      rw [poll_at _ j k z h i]; change p (wrap n z,y,i)=p (toPAC.symm (toPAC (wrap n z,y,i))); rw [Equiv.symm_apply_apply]
    rw [stepValue,PiLp.sub_apply,hx,hx,map_add,wrap_step]
  unfold nursery
  simp only [Pi.add_apply,PiLp.add_apply]; rw [he b c hb,he a b ha]
  rw [show stepValue (polar (nativeChart p) c a) b= -stepValue (polar (nativeChart p) a c) b from funext fun i=> by nth_rw 1 [Beamer.reverse]; simp [stepValue]; abel,Pi.neg_apply,PiLp.neg_apply,he a c (ha.trans hb)]; abel

theorem shutters (p : Incidence G n → ℝ) :
    shutter (nativeChart p) ↔ tensor G (Exterior.d 2 n)*ᵥliftPAC p=0 := by
  constructor
  · intro h; funext ⟨x,T,i⟩; obtain ⟨a,b,c,ha,hb,rfl⟩:=cube_hits T
    have ht (a b c:Axis):nursery (nativeChart p) a b c=0:= h a b c
    have hh:= linked_cube p a b c ha hb i (lift x); rw [wrap_lift,ht] at hh
    exact hh.symm
  intro h; apply sufficient; intro a b c ha hb; ext1 x; ext i; rw [linked_cube p a b c ha hb,h]; rfl

section release
variable (A : Levels G) (N p k : ℕ)
lemma rows_close (i : Chamber G A.S k p) :
    shutter (Radian.wall_chart (P:=A.S) (p:=p) (k:=k) fun j => (((stamp A N p).κ k).cov i j).re) := by
  let H:=complete A N k p; let n:=A.S.side k p; let D:=tensor G (Exterior.d 2 n)
  rw [← chart_eq, shutters]
  have he : liftPAC (fun j => (((stamp A N p).κ k).cov i j).re)=fun j => H j (toPAC i) := by
    ext j; rw [liftPAC,Function.comp_apply,stamp_pairs]; simp only [Complex.ofReal_re,Equiv.apply_symm_apply]; exact congr_fun (congr_fun (symmetric_complete A N k p) j) _
  rw [he]; funext j; change (D*H) j _=_; rw [show D*H=0 from complete_closed ..]; rfl

lemma fiscal (u v : Cover) :
    let X := (stamp A N p).κ k
    (∀ i,shutter (Prayer.looked X u v i))∧ (∀ i, shutter (fun j=> Prayer.looked X u v j i)) := by
  intro X; constructor
  · intro i; exact Radian.shuttered _ (rows_close A N p k (body u i)) v
  intro i; rw [show (fun j => Prayer.looked X u v j i)=Prayer.looked X v u i from funext fun j => congr_arg Complex.re (X.symm _ _)]; exact Radian.shuttered _ (rows_close A N p k (body v i)) u
end release
end YM.PhysicalNext.RankCovariance

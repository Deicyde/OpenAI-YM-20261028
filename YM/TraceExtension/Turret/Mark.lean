import YM.TraceExtension.Turret.Pint
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Turret
open Function Filter Matrix Lattice Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp Extra.Iteration
open Filch
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}{k r:ℕ}{o x y:Site n}{p q C E D a v:ℝ}{Z:Dart G n}{R:PathData G}{s:Clip}
abbrev Sway(G:Gauge)(n:Side):= Axis→Axis→CrG G n
def mine (r:ℕ)(X:Sway G n): Sway G n:= fun i j=> frost (X i j) r
def pluck (r:ℕ)(Z:Dart G n)(k:Axis):= frost (Z.Q k) r
def pluckD (r:ℕ)(Z:Dart G n)(i j k:Axis):= frost (Z.twist i j k) r
def aimD := (univ:Finset Axis).erase 0
private lemma afact : (aimD.card:ℝ)=3:=by unfold aimD; simp

def paceX(r:ℕ)(Z:Dart G n): Sway G n := fun a b=> if a=0∧b=0 then (∑ i,twing i)-(∑ i∈aimD,mine r Z.J i i) else if b<a then (mine r Z.J b a)-∑ i:Axis,twig i (pluckD r Z b a i) else mine r Z.J a b
 where twing i:=twig i (pluck r Z i)
lemma unitst(r:ℕ)(Z:Dart G n):paceX r Z 0 0=(∑ i, twig i (pluck r Z i))-(∑ i∈aimD,mine r Z.J i i):=by rw [paceX,if_pos ⟨rfl,rfl⟩];rfl
lemma aim_ne (x:Axis)(h:x∈aimD):x≠0:=ne_of_mem_erase h
lemma picks (r:ℕ)(Z:Dart G n): (∑ i∈aimD,paceX r Z i i)=(∑ i∈aimD,mine r Z.J i i):=by apply sum_congr rfl; intro i hi; unfold paceX; simp[aim_ne i hi]
lemma cones(r:ℕ)(Z:Dart G n): ∑ i:Axis,paceX r Z i i= ∑ i,twig i (pluck r Z i):=by
    let F i:=paceX r Z i i; rw [← Finset.add_sum_erase (a:=0) _ F (mem_univ _)];change F 0+∑ i∈aimD,F i=_;rw[picks r Z,show F 0=_ from unitst r Z, sub_add_cancel]
lemma spirit(r:ℕ)(Z:Dart G n)(i j:Axis)(h:i< j): paceX r Z i j - paceX r Z j i= ∑ k, twig k (pluckD r Z i j k):=by
   unfold paceX; rw[if_neg, if_neg (not_lt.mpr h.le),if_neg,if_pos h,sub_sub_cancel]; all_goals intro hr; obtain ⟨rfl,rfl⟩:=hr; exact (lt_irrefl _ h)
private lemma untw(h:Z.Sound R s): Z.J 0 0=(∑ i, twig i (Z.Q i))-∑ i∈aimD,Z.J i i:= by
    apply eq_sub_of_add_eq; exact (Finset.add_sum_erase _ (fun i=>Z.J i i) (mem_univ 0)).trans h.hue

def plumAmount(A:ℝ):=4*(A+A)+4*A+A
def papa(A:ℝ):= 4*(Perfect.shelter 1 4 1*A + A)+4*A+A
lemma pulse (ht:BurstG G k r a p D C E) (hZ:Viz Z s R a (fun _=>p) (fun _=> q) v) (hx:Z.March)(ha:0 ≤ a)(he:a ≤ 1)(hC:0 ≤ C)(hE:0 ≤ E):
    (∀ i, Bond (Z.Q i) (pluck r Z i) k (4*(r+1+1)) (a/100) C E D) ∧ (∀ i j k',Bond (Z.twist i j k') (pluckD r Z i j k') k (4*(r+1+1)) (a/100) C E D)∧∀ i j,Bond (Z.J i j) (paceX r Z i j) k (4*(r+1+1)+1) (a/100) (plumAmount C) (papa E) D:=by
   let Y:=Z.J
   have h(i j):Bond (Z.J i j) (mine r Z.J i j) k (4*(r+1+1)) _ C E D:=ht n _ (fun x=> congr_arg (fun a:Dart G n=> a.J i j) (hx.still x)) (hZ.sound.heart i j _) (hZ.J i j _)
   have hp(i):Bond (Z.Q i) (pluck r Z i) k (4*(r+1+1)) _ C E D:=ht n _ (fun x=> congr_arg (fun a:Dart G n=> a.Q i) (hx.still x)) (hZ.sound.plumQ i _) (hZ.plum i _)
   have hz(i j k'):Bond (Z.twist i j k') (pluckD r Z i j k') k (4*(r+1+1)) _ C E D:=ht n _ (fun x=> congr_arg (fun a:Dart G n=> a.twist i j k') (hx.still x)) (hZ.sound.mint i j k' _) (hZ.mint ..)
   have hA :0≤ a/100:=by positivity
   have hA' : a/100 ≤ 1:=by linarith only[he]
   have ht:= Perfect.shelter_pos (1:ℝ) 4 zero_le_one
   refine ⟨hp,hz,fun i j=>?_⟩; by_cases hD:i=0∧j=0
   · obtain ⟨rfl,rfl⟩:=hD; rw[unitst,untw hZ.sound]; apply ((Bond.bondS _ _ _ _ _ (fun i _=> (hp i).suffix i hA hA')).lapse (Bond.bondS _ _ _ _ _ (fun i _=> (h i i).top le_rfl le_rfl (Nat.le_succ _)))).top _ _ le_rfl
     · simp only[sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; rw[afact]; unfold plumAmount; norm_num [Axis]; linarith
     simp only[sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]; rw [afact]; unfold papa; norm_num [Axis]; linarith
   unfold paceX; rw [if_neg hD]; split <;> rename_i H
   · rw[show Z.J i j= Z.J j i-(∑ l,twig l (Z.twist j i l)) from by rw [← hZ.sound.tint]; abel]
     apply (((h j i).top le_rfl le_rfl (Nat.le_succ _)).lapse (Bond.bondS _ _ _ _ _ (fun u _=> (hz j i u).suffix u hA hA'))).top _ _ le_rfl
     · norm_num [Axis,plumAmount]; linarith
     norm_num [Axis,papa]; linarith
   refine (h i j).top (by unfold plumAmount; linarith only[hC]) (by unfold papa; nlinarith only [hE,mul_nonneg ht.le hE]) (Nat.le_succ _)
end YM.Trace.Turret

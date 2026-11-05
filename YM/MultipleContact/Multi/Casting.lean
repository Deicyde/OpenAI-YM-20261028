import YM.MultipleContact.Multi.Signs
import YM.Euclid.Lift
/-! Field-linear insertion identity and movement of actual separated profiles in placement algebra. -/
set_option autoImplicit false
set_option maxHeartbeats 1500000
noncomputable section
namespace YM.MultipleContact.Scene
open Function Filter Set MeasureTheory Lattice Extraction Ward Table Script
open scoped Topology BigOperators InnerProductSpace ContDiff Classical
variable {G:Gauge}{L:Register G}(S:Table L){n m d:ℕ}
local notation "Loc" => Alpha S
local notation "Gram" => Grammar (Alpha S)
def call(v:Fin n→S.Tag)(x:Fin n→ E4):Gram:=spell (fun i:Fin n=>(v i,x i))
lemma call_secure {v:Fin n → S.Tag}{x:Fin n→ E4}{U:Set E4}(hx:Injective x)(hr:Set.range x ⊆U):Secure S U (call S v x):=secure_spell S hr hx
private lemma stamp_eq (w:Loc):stamp w=spell (fun _:Fin 1=>w):=by unfold spell; simp

theorem inline (hs:S.Symmetric)(s:E4)(a:Gram):∃ f:S.Field d→ₗ[ℂ]ℂ,∀v:S.Field d,evaluation S (stamp ((⟨d,v⟩:S.Tag),s)*a)=f v:=by
   have heq (v:S.Field d)(m:ℕ)(t:Fin m → Loc): stamp ((⟨d,v⟩:S.Tag),s) * spell t = spell (Fin.append (fun _:Fin 1=>((⟨d,v⟩:S.Tag),s)) t):=by rw [spell_sum (fun (_:Fin 1)=> ((⟨d,v⟩:S.Tag),s)) t, ← stamp_eq]
   let xp (m) (t:Fin m→ Loc):=points (fun j:Fin (1+m)=> ((Fin.append (fun (_:Fin 1)=>((⟨d, (0:S.Field d)⟩:S.Tag),s)) t) j).2)
   let q m (t:Fin m→Loc):= fun j:Fin (1+m)=> ((Fin.append (fun (_:Fin 1)=>((⟨d, (0:S.Field d)⟩:S.Tag),s)) t) j).1
   let a0(m):Fin (1+m):=Fin.castAdd m (0:Fin 1)
   let f(m:ℕ)(t:Fin m→Loc):S.Field d→ₗ[ℂ]ℂ:=if xp m t ∈ conf _ then Ward.here (q m t) (xp m t) (a0 m) d else 0
   have hP (l:ℕ)(i:Fin l):Fin.natAdd 1 i≠ a0 l:=fun h=>by have h:= congr_arg Fin.val h; change 1+(i:ℕ)=0 at h; omega
   have hy' (m:ℕ)(t:Fin m→Loc)(v:S.Field d):evaluation S (stamp (⟨d,v⟩,s)*spell t)=f m t v:=by
        rw [heq,eval_fin S hs,read_points]
        have he₁ : (fun _ : Fin 1=> ((⟨d,v⟩:S.Tag),s))= fun _=> ((⟨d,v⟩:S.Tag),s):=rfl -- remove
        have he₂ : (points fun j => (Fin.append (α:=Loc) (fun _=>((⟨d,v⟩:S.Tag),s)) t j).2) = xp m t:=by ext1 i; exact Fin.addCases (fun i=>by simp [xp]) (fun i=>by simp [xp]) i
        rw [he₂]
        unfold Truncated f; split_ifs with h -- if props mismatch?
        · dsimp only; rw [Ward.takes]; unfold Ward.disc; congr 1
          funext i; exact Fin.addCases (fun k=>by fin_cases k; simp [a0]) (fun j=> by simpa only [q,Function.update_of_ne (hP m j),Fin.append_right] ) i -- hP misuse
        rfl
   refine ⟨∑ m∈a.coeff.support,a.coeff m • f m.card (pickFrame S m), fun v=>?_⟩
   nth_rw 1 [sum_terms a,Finset.mul_sum,map_sum]
   rw [LinearMap.sum_apply]
   exact Finset.sum_congr rfl fun m _=> (by rw [mul_smul_comm,map_smul,LinearMap.smul_apply]; exact congr_arg ((a.coeff m) • ·) (hy' m.card ((letters_frame m).choose) v))
lemma inline_smul (hs:S.Symmetric)(s:E4)(a:Gram)(c:ℂ)(v:S.Field d):evaluation S (stamp ((⟨d,c • v⟩:S.Tag),s)*a)=c • evaluation S (stamp (⟨d,v⟩,s)*a):=by obtain ⟨f,hf⟩:=inline (d:=d) S hs s a; rw [hf,hf]; exact f.map_smul c v

lemma append_clear {ι:Type*}(v:Fin n→ι)(t:Fin m→ι)(hv:Injective v)(ht:Injective t)(h:∀ i:Fin n,∀j:Fin m,v i≠t j):Injective (Fin.append (α:=ι) v t):=by
   intro i j; revert j
   refine Fin.addCases ?_ ?_ i
   · intro i k
     refine Fin.addCases (m:=n) (n:=m) (motive:=fun k=> Fin.append v t (Fin.castAdd m i)=Fin.append v t k → Fin.castAdd m i=k) (fun j hl=>by
           apply congr_arg (Fin.castAdd _); apply hv;simpa using hl) (fun j hl=>(h i j (by simpa using hl)).elim) k
   intro i k
   refine Fin.addCases (m:=n) (n:=m) (motive:=fun k=> Fin.append v t (Fin.natAdd n i)=Fin.append v t k → Fin.natAdd n i=k) (fun j hl=>(h j i (by simpa using hl.symm)).elim) (fun j hl=>by
         apply congr_arg (Fin.natAdd _); apply ht;simpa using hl) k

def moved (u:E4)(x:Fin n → E4)(k:Fin n)(j:Axis)(a t:ℝ):= fun i:Fin n=>u+ Function.update x k (x k + t • (a • basis j)) i
lemma moved_zero (u:E4)(x:Fin n → E4)(k:Fin n)(j:Axis)(a:ℝ): moved u x k j a 0=fun i=>u+x i:=by unfold moved; simp
lemma line_change {u:E4}(x:Fin n→E4)(z:Fin m→E4)(k:Fin n)(j:Axis)(a t:ℝ): let f(t:ℝ):=points (Fin.append (moved u x k j a t) z); f t= f 0 + t • (a • Points.direction (Fin.castAdd m k) j):= by
      intro f;ext1 i; change f t i=_
      let E:=Fin.castAdd m k
      have hu(i:Fin m):E ≠ Fin.natAdd n i:=fun e=>by have e:=congr_arg Fin.val e; dsimp [E] at e; change (k:ℕ)=n+(i:ℕ) at e; have e':=k.isLt; omega
      exact Fin.addCases (fun i=> by
         by_cases h:i=k <;> simp only [f,moved,points_apply,Fin.append_left,PiLp.add_apply,PiLp.smul_apply]
         · simp [h,add_assoc,Points.direction]
         have he:E ≠ Fin.castAdd m i:= (Fin.castAdd_injective n m|>.ne (Ne.symm h))
         simp [Points.direction,E,PiLp.single_apply,h,Function.update_of_ne h, he]) (fun j=>by simp [f,Points.direction,PiLp.single_apply,hu j,E]) i
-- primitive separated derivative. R is inactive-placement region; note: no Ward assertion at collisions.
variable {P:DiffPlan S}(H:S.Hierarchy)(hP:P.Derivatives S)
include H hP
lemma moving_call (v:Fin n→S.Tag)(u:E4)(y:Fin n → E4)(t:Fin m→ Loc) (k:Fin n)(q:Axis)(a:ℝ)(s:ℝ)
    (hp:Injective (fun i=> (t i).2))
    (hcur:Injective (moved u y k q a s))
    (hinj:∀i:Fin n,∀j:Fin m, (moved u y k q a s) i ≠ (t j).2):
    HasDerivAt (fun w=>evaluation S (call S v (moved u y k q a w)*spell t))
        (a • evaluation S (call S (Function.update v k (Ward.rise P q (v k))) (moved u y k q a s)*spell t)) s:= by
       let z b := points (Fin.append (moved u y k q a b) (fun i=> (t i).2)); let d:= Fin.append (α:=S.Tag) v (fun i=> (t i).1); let v':=Function.update v k (Ward.rise P q (v k)); let d':= Function.update d (Fin.castAdd m k) (Ward.rise P q (d (Fin.castAdd m k)))
       have he (w:ℝ): call S v (moved u y k q a w)*spell t=spell (Fin.append (fun i=>(v i,(moved u y k q a w) i)) t):=(spell_sum ..).symm
       have h' (v:Fin n→S.Tag)(w):evaluation S (call S v (moved u y k q a w)*spell t) = Truncated S (z w) (Fin.append (α:=S.Tag) v (fun j=>(t j).1)):=by
                rw [show call S v _ * spell t =spell _ from (spell_sum _ t).symm, eval_fin S H.laws.toSymmetric, read_points]; congr 1
                · ext1 i; exact Fin.addCases (fun j=>by simp [z]) (fun j=>by simp [z]) i
                exact funext fun i=> Fin.addCases (fun j=>by simp) (fun j=>by simp) i
       let i:= Fin.castAdd m k;let dir:=Points.direction i q
       have heD : HasDerivAt z (a • dir) s:=by
            rw [show z=fun r=>z 0+r • (a • dir) from (by funext; exact line_change y (fun i=>(t i).2) .. )] -- t shadow
            exact (hasDerivAt_const_add_iff _).mpr (show HasDerivAt (ContinuousLinearMap.toSpanSingleton ℝ (a • dir)) _ _ from
             (ContinuousLinearMap.toSpanSingleton ℝ (a • dir)).hasDerivAt.congr_deriv (by simp))
       have ht : z s ∈ conf _:= append_clear _ _ hcur hp hinj
       have hq := ((cont_disc H d ht).differentiableAt (by simp)).hasFDerivAt.comp_hasDerivAt s heD
       have hj:Ward.disc d' (z s)=Analysis.D dir (Ward.disc d) (z s):=by symm; exact Ward.fromD P H hP ht i q d
       have hf : d'= Fin.append (α:=S.Tag) v' (fun i=>(t i).1):=by
             funext p; unfold d' d; rw [Fin.append_left]; refine Fin.addCases (fun j=>?_) (fun j=>?_) p
             · by_cases h:j=k
               · rw [h]; simp [v']
               simp [Function.update_of_ne ((Fin.castAdd_injective n m).ne h),Function.update_of_ne h,v']
             have hi:Fin.natAdd n j ≠ Fin.castAdd m k:=fun e=>by have e:=congr_arg Fin.val e;change n+(j:ℕ)=(k:ℕ) at e; have h:=k.isLt; omega
             simp [Function.update_of_ne hi]
       rw [h' v' s]; change HasDerivAt _ (a • Truncated S (z s) _) s; rw [Truncated,if_pos ht,← hf]
       change HasDerivAt _ (a • disc d' (z s)) _; rw [hj]
       have hr : ∀ᶠ t in 𝓝 s, z t∈conf _:= heD.continuousAt.eventually ((conf_open _).mem_nhds ht)
       apply (Filter.EventuallyEq.hasDerivAt_iff (show (fun w => evaluation S (call S v (moved u y k q a w) * spell t)) =ᶠ[𝓝 s] (disc d ∘ z) from ?_)).mpr
       · simpa only [_root_.map_smul, Analysis.D] using hq -- replace
       filter_upwards [hr] with b hb; rw [h',Truncated,if_pos hb]; rfl
end YM.MultipleContact.Scene

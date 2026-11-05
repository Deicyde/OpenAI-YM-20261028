import YM.MultipleContact.Matching.Continuum
import YM.MultipleContact.Bunch.Grid

set_option autoImplicit false
noncomputable section
namespace YM.MultipleContact.Bunching
open Filter Function MeasureTheory Analysis Extraction Table Ward MergeProof Ribbons Around Cells Wilson Lattice Work.A01
open scoped Topology BigOperators Classical
open YM.Next.UVStress Matching Local

lemma continuous_lands {n m:ℕ} (y:Fin n → E4):Continuous (lands y : Points m → Points (n+m)):= by
   apply (PiLp.continuous_toLp 2 (fun _:Fin (n+m)=>E4) ).comp (show Continuous (fun z:Points m=>Fin.append y z) from ?_)
   apply continuous_pi
   intro i; refine Fin.addCases ?_ ?_ i
   · exact fun j=>show Continuous (fun z:Points m=>(Fin.append y z) (Fin.castAdd m j)) from by simp only [lands,points_apply,Fin.append_left]; exact continuous_const
   exact fun j=>show Continuous (fun z:Points m=> (Fin.append y z) (Fin.natAdd n j)) from by simpa only [lands,points_apply,Fin.append_right] using! (PiLp.continuous_apply 2 (fun _:Fin m=>E4) j: Continuous (fun z:Points m=>z j))

section shift
variable {m:ℕ}
private def gridshift (z: Points m) (Q:Schedule) (k:ℕ):Points m:=z+Q.a k • (points (fun x:Fin m=> (WithLp.toLp 2 fun i:Axis =>(x.val+1:ℝ))))
private lemma grid_tends (z:Points m)(Q:Schedule): Tendsto (gridshift z Q) atTop (𝓝 z):=by
    simpa [gridshift] using! (Q.shrinks.smul_const ((points fun x:Fin m=> (WithLp.toLp 2 fun i:Axis =>((x.val:ℝ)+1:ℝ))) : Points m) |>.const_add z)
private lemma grid_avoids (z:Points m)(Q:Schedule)(x:Fin m)(a:Axis)(c:ℝ):∀ᶠ k:ℕ in atTop,c≠ gridshift z Q k x a:=by
       by_cases he:z x a=c
       · filter_upwards with k; rw [show gridshift z Q k x a=z x a+Q.a k * (↑x+1) from rfl,he]; exact ne_of_lt (lt_add_of_pos_right _ (by have h:=Q.a_pos k; positivity))
       exact ((((show Continuous (fun w:Points m=>w x a) from by fun_prop).tendsto z).comp (grid_tends z Q)).eventually (isOpen_ne_fun continuous_const continuous_id|>.mem_nhds (fun h=>he h.symm)))
private lemma grid_generic (z:Points m)(Q:Schedule):∀ᶠ k:ℕ in atTop,(gridshift z Q k)∈generic m:=by
       have h (p:{x:Fin m×Fin m | x.1≠x.2})(a:Axis): ∀ᶠ k:ℕ in atTop, (gridshift z Q k p.val.1 a ≠ gridshift z Q k p.val.2 a):=by
          let x:=p.val.1; let u:=p.val.2
          by_cases h:z x a=z u a
          · have hh:(x:ℝ)≠(u:ℝ):=by exact_mod_cast (show x.val≠u.val from fun he=>p.property (Fin.ext he))
            filter_upwards with k
            change z x a+Q.a k * ((x.val:ℝ)+1)≠ z u a+Q.a k * ((u.val:ℝ)+1)
            rw [h]; intro he; exact hh (by nlinarith only [he,Q.a_pos k])
          have ht (v:Fin m):= ((show Continuous (fun w:Points m=>w v a) from by fun_prop).tendsto z).comp (grid_tends z Q)
          exact ((ht x).prodMk_nhds (ht u)).eventually (isOpen_ne_fun continuous_fst continuous_snd |>.mem_nhds h)
       filter_upwards [eventually_all.mpr fun p=>eventually_all.mpr (h p)] with k h a i j he
       by_contra hz; exact h ⟨(i,j),hz⟩ a he
private lemma grid_joint (n:ℕ)(y:Fin n → E4)(hy:∀a:Axis,Injective (fun i:Fin n=> y i a))(z:Points m)(Q:Schedule):∀ᶠ k in atTop,lands y (gridshift z Q k)∈generic _:=by
       filter_upwards [grid_generic z Q, eventually_all.mpr fun i=> eventually_all.mpr fun a=>eventually_all.mpr fun j=>grid_avoids z Q j a (y i a)] with k hk hh
       have h1(j:Fin n): lands y (gridshift z Q k) (Fin.castAdd m j)=y j:=by simp [lands]
       have h2(j:Fin m): lands y (gridshift z Q k) (Fin.natAdd n j)=gridshift z Q k j:=by simp [lands]
       intro a x v; revert v; refine Fin.addCases ?_ ?_ x
       · intro x v; exact Fin.addCases (fun v h=>congr_arg (Fin.castAdd m) (hy a (by simpa only [h1] using h))) (fun v h=> (hh x a v (by simpa only [h1,h2] using h)).elim) v
       intro x v; exact Fin.addCases (fun v h=>(hh v a x (by simpa only [h1,h2] using h.symm)).elim) (fun v h=> congr_arg (Fin.natAdd n) (hk a (by simpa only [h2] using h))) v
lemma generic_cons_of {n:ℕ}[Inhabited (Fin n)]{y:Fin n→ E4}{z:Points m}(hy0:y default=0)(h:lands y z ∈ generic _):Points.cons 0 z∈generic _:=by
       have hc(a) (j:Fin m):z j a≠0:=fun he=>by
            have heq : lands y z (Fin.natAdd n j) a=lands y z (Fin.castAdd m (default:Fin n)) a:=by simpa only [lands,points_apply,Fin.append_left,Fin.append_right,hy0,PiLp.zero_apply] using he
            have e:= congr_arg Fin.val (h a heq); simp at e; have hh: (default:Fin n).val<n:=Fin.isLt _; omega
       intro a; refine fun i j => Fin.cases (Fin.cases (fun _=>rfl) (fun i h=>(hc a i (by simpa [Points.cons,Fin.cons_succ,Fin.cons_zero] using h.symm)).elim))
             (fun j=>Fin.cases (fun h=>(hc a j (by simpa [Points.cons] using h)).elim) (fun i h'=>?_)) i j
       have heq:lands y z (Fin.natAdd n j) a=lands y z (Fin.natAdd n i) a:=by simpa only [lands,points_apply,Fin.append_right,Points.cons,Fin.cons_succ] using h'
       have he: j=i := Fin.ext (by have e:= congr_arg Fin.val (h a heq); simp at e; omega)
       exact congr_arg Fin.succ he
end shift

variable {G:Gauge}{C:Family G}{S:Table C.book}{F:Extraction.Order} {D J n':ℕ}
variable {ι:Type*}{n:ι→ℕ}
variable (q:∀i:ι,Fin (n i)→ C.book.Token) (ℓ:∀i:ι,Fin (n i)→ Cover)
variable (hc:S.Hierarchy)(hp:F.PointLimits C S)
variable (hq:Cells.CellHyp C F)(hC:C.Makes)
variable {r A1 A2 h wt:ℝ}
include hc in
private lemma closes {zctx:∀i,Points (n i)}{yPoint:Fin n' → E4}{z':ℕ→∀i,Points (n i)}(ht:∀i,Tendsto (z' · i) atTop (𝓝 (zctx i)))(hs:∀i,Points.cons 0 (zctx i)∈conf _)
       (hconf:∀i,lands yPoint (zctx i)∈conf _) {V':Fin n' → S.Tag}(he:∀ᶠ k:ℕ in atTop, ∃ v:S.Field D, bondedMany q V' yPoint wt D (z' k) v A1 A2):∃ v:S.Field D,bondedMany q V' yPoint wt D zctx v A1 A2:=by
       classical
       let v (k:ℕ) := if H : ∃w:S.Field D,bondedMany q V' yPoint wt D (z' k) w A1 A2 then H.choose else 0
       have hb:∀ᶠ k in atTop, bondedMany q V' yPoint wt D (z' k) (v k) A1 A2:=by
          filter_upwards [he] with k h
          dsimp [v]; rw [dif_pos h]; exact h.choose_spec
       obtain ⟨b,hB,hh,w,Hw⟩:=finite_extract (𝓛:=atTop) v A1 (hb.mono fun _ h=>h.1)
       refine ⟨w,le_of_tendsto Hw.norm (((hb.mono (fun _ h=>h.1))).filter_mono hB), fun i=>le_of_tendsto (x:=b) ?_ (((hb.mono (fun _ h=>h.2 i))).filter_mono hB)⟩
       have ht(i):= (ht i).mono_left hB
       have hf:=(once_tends (q i) _ (hs i) w hc).tendsto.comp ((ht i).prodMk_nhds Hw)
       have hx:= (continuous_lands yPoint).tendsto (zctx i)
       exact ((Tendsto.const_smul ((cont_disc hc _ (hconf i)).continuousAt.tendsto.comp (hx.comp (ht i))) wt |>.sub hf).norm)
variable (hL:∀ i,Injective (Fin.cons (α:=fun _=>Cover) 0 (ℓ i))) (hr:0<r)
include hc hp hC hq hL hr
set_option quotPrecheck false

variable [inh:Inhabited (Fin n')] (d:Fin n'→ℕ)
-- axis conditions for y' are not modulo torus size; period tends first to infinity.
variable {lamp:Lattice.Side}
lemma comparableMany [Fintype ι]:∃am> (0:ℝ),∀ V (m j D:ℕ), ∀ h A1 A2:ℝ, Bunching.Box C J j m D d h V F lamp A1 A2 →
    ∀ y':Fin n' → Cover, y' default=0 → (∀s t,s≠t → (fuga C.path.levels (m+1))/16≤ ‖C.S.gridPoint j (y' s-y' t)‖)→ (∀ s,‖C.S.gridPoint j (y' s)‖≤4*topZone C.path.levels (lamp*C.S.block m) (m+1)) →
    ∀z:∀i,Points (n i), (∀ i,Locations C J r (ℓ i) (z i))→ (∀ i,lands (C.S.gridPoint j ∘ y') (z i)∈conf _) →
          (∀a:Axis,Injective (fun b=>C.S.gridPoint j (y' b) a))→
          ∃ v:S.Field D, bondedMany q (fun i=>⟨d i,S.project (d i) (V i)⟩) (C.S.gridPoint j ∘ y') ((fuga C.path.levels (m+1))^h) D z v (‖LinearMap.toContinuousLinearMap (S.project D)‖* A1) (am*A2):=by
    obtain ⟨am,hA,Ha⟩:=readGrid (lamp:=lamp) (d:=d) (J:=J) hc hp q hq hC ℓ hL hr
    refine ⟨am,hA,fun V m j D h A1 A2 hBox y hx0 h₁ h₂ z hZ hy hne=>?_⟩
    let b:=C.S.gridPoint j ∘ y
    have heq: b default=0:=by unfold b; dsimp only [Function.comp_apply]; rw [hx0]; ext1 i; change C.S.a j*((↑(0:ℤ)):ℝ)=0;simp -- rfl?
    have hsaf(i): Points.cons 0 (z i)∈conf _:=by
       have hn(p:Fin (n i)):0≠z i p:= fun he=>by
            have heq': lands b (z i) (Fin.castAdd (n i) (default:Fin n'))=(lands b (z i)) (Fin.natAdd n' p):=by simpa [lands,heq] using he
            have ht:=(congr_arg Fin.val ((hy i) heq')); simp at ht
            have hh: (default:Fin n').val<n':=Fin.isLt _; omega
       rintro x x' hh; revert x' hh; refine Fin.cases (Fin.cases (fun _=>rfl) (fun i h=>(hn i h).elim)) (fun i'=> ?_) x
       refine Fin.cases (fun h=>(hn i' h.symm).elim) (fun pt h=>?_) -- binder x implicit
       have ht':=(hy i) (show lands b (z i) (Fin.natAdd n' i')=lands b (z i) (Fin.natAdd n' pt) from (by change z i i'=z i pt at h; simpa [lands] using h))
       have ht:=congr_arg Fin.val ht'; simp at ht; exact congr_arg Fin.succ (Fin.ext ht)
    let z' k i:=gridshift (z i) C.S k
    have hz'(i): Tendsto (z' · i) atTop (𝓝 (z i)):=grid_tends ..
    apply closes q hc hz' hsaf hy
    have hc' (i) : ∀ᶠ k in atTop, Locations C J r (ℓ i) (z' k i):=locations_open ℓ (hz' _) (hZ i)
    have hg (i) : ∀ᶠ k in atTop, lands b (z' k i) ∈ generic _ := grid_joint n' b hne _ _
    filter_upwards [eventually_all.mpr hg,eventually_all.mpr hc'] with k hk hk'
    let Z:= z' k; let Gm(t i):= Extraction.Order.grid C t (address (C.S.a t) (Z i))
    let u (i) : Points (n i) → Points _ := lands b
    let v (t i):= address (C.S.a t) (Z i)
    have hT(i):Tendsto (Gm · i) atTop (𝓝 (Z i)):= chosen _
    have hO(i):∀ᶠ t in atTop,u i (Gm t i) ∈ generic _:= ((continuous_lands b).continuousAt.tendsto.comp (hT i)) |>.eventually ((genericOpen _).mem_nhds (hk i))
    apply closes q hc hT (fun i=>generic_conf _ (generic_cons_of heq (hk i))) (fun i=>generic_conf _ (hk i))
    filter_upwards [eventually_all.mpr hO,eventually_all.mpr fun i=> locations_open ℓ (hT i) (hk' i)] with t ht hu
    apply Ha V _ _ _ _ _ _ hBox (v t) t (fun i=>?_) y hx0 h₁ h₂ _ (fun i=>rfl) hu ht
    rw [show Extraction.Order.grid C t (Fin.cons 0 (v t i))= Points.cons 0 (Gm t i) from ?_]
    · exact generic_cons_of heq (ht i)
    ext1 j; refine Fin.cases ?_ (fun k=>rfl) j
    change C.S.gridPoint t 0=0
    ext1 i; change C.S.a t*((↑(0:ℤ)):ℝ)=0; simp
end YM.MultipleContact.Bunching

import YM.TraceExtension.Fen.Prongs
set_option autoImplicit false
noncomputable section
namespace YM.Trace.Fen
open Function Filter Matrix Lattice Pressure Ac Wilson RG Precision Laurent Stationary Perfect Exterior Tree RG Wilson Finset Push.Uniform Det Planned.PrimaryIntegral295 Lamp
open Filch Turret Shepherd AnalyticBridge VerifiedReset Drupes Extra.Iteration SectorAffine
open scoped BigOperators Topology ContDiff Matrix.Norms.Frobenius Classical
variable {G:Gauge}{n:Side}(R:Rep G n){I:Type}(b:I→Barley) {k:ℕ}{σ a A C D E p q v u w:ℝ}
lemma wing_zero (j:Barley):(ul R.path R.clip j (0:Site n)) 1=0:=by
    cases j with
    | inr j=>
        rw [fresh_loop]; have hh(i:Fin (rowD j)): ((tooth R j).leg i).atSite (1:Config G n) 0=0:=by rw [Work.F03.atSite_path,WilsonStartup.face_one ]; simp
        have he: rowD j≠0:=by cases j with
           | inl s=> cases s<;> norm_num[rowD,High.arity]
           | inr i=> exact two_ne_zero
        simp [Atom.unmasked,hh,Atom.poly,he]
    | inl j=>
       change Low.mark _ _ _*Low.plain _ _ _ _=_; have h(s:RG.Slot):s.atSite (1:Config G n) 0=0:=by rw [Work.F03.atSite_path,WilsonStartup.face_one]; simp
       rw [show Low.plain R.path j 0 (1:Config G n)=0 from ?_,mul_zero]; simp only [Low.plain,h,WilsonStartup.face_one,G.price_one,inner_zero_left,zero_div]; cases j.2 <;> simp
lemma clergyP (J:Peat G n)(hp:GaugeInvariant J)(hs:ContDiffAt ℝ ω (J ∘ input G n) 0)(h:J 1=0)(hG:G.Simple):J∈loom G n:=by
    have ht:Cleric J:=⟨hs,fun _ _ _ _ _ _ _ _ _ _ _ _=> Eventually.of_forall fun _=>hp ..⟩
    refine ⟨ht,fun i hi=>?_⟩; interval_cases i <;> ext1 v
    · simp only[iteratedFDeriv_zero_apply,Function.comp_apply,input_zero,h]
    simp only[iteratedFDeriv_one_apply,dyed_hold ht hG,fderiv_fun_const]; rfl
lemma ferB (s:Seat n)(b:Barley)(h:R.path.Bounds R.clip σ A C) (hG:G.Simple): fer R s b∈loom G n:=by
    apply clergyP _ (ferInv R s b h) (lick R id (s,b) (input G n) _ (Army.powL (v:=id) contDiffAt_id)) _ hG
    unfold fer; rw [show s.view (1:Config G n)=1 from ?_, wing_zero,mul_zero]; change pull s.1 s.2 (1:Config G n)=_; funext i; unfold pull Step.read; split; exact _root_.inv_one; rfl
variable (Q:Support n)(L:Finset I) (x:Site n)
def flocks:= (univ (α:=Seat n) ×ˢ L).filter (fun i : Seat n × I=> ¬Disjoint Q (Tar R b i))
def prun: Peat G n:=∑ p∈flocks R b Q L,seatP R b p
lemma pruned (e: Lines G n 1)(hp:e.1 ∈Q)(he:2≤ R.p.B): outD (piste R b L) e=outD (prun R b Q L) e:=by
    rw[overlook]; funext U; unfold outD prun; simp only [Finset.sum_apply]
    rw [fderiv_fun_sum (fun i _=> licks R b i U), _root_.sum_apply]; apply Eq.symm (sum_subset (filter_subset ..) ?_)
    intro i hi h; exact out_home e (licks R b i U) _ (ferLocal R _ _ he) (fun he=> h (mem_filter.mpr ⟨hi, not_disjoint_iff.mpr ⟨_,hp,he⟩⟩))
def salo (a r:ℕ):=1800*(R.p.B+r)+a
-- finite trunc.Splendor sufficient rill_core. beta outside.A_path measure.Payment.
lemma angel (p:Seat n×I)(a r:ℕ)(h:p∈ flocks R b (sprout x a) (spikes R b L r)): Tar R b p ⊆ sprout x (salo R a r):=by
    obtain ⟨hh,ht⟩:= mem_filter.mp h; obtain ⟨y,hy,hv⟩:=not_disjoint_iff.mp ht
    obtain ⟨v,hv',he⟩:= halo_spec.mp hy
    rw[mem_singleton.mp hv'] at he
    have hg:mote R (b p.2) ≤ r:= (mem_filter.mp (mem_product.mp hh|>.2)).2
    exact (surrounds R p.1 (b p.2) y hv).trans ((hedge he _).trans (sprout_mono x (by unfold salo; omega)))
lemma policy (G:Gauge)(k:ℕ)(E:ℝ)(hE:0≤ E) :∃ f:ℝ, ∃ u:ℕ,1 ≤ f ∧ ∀ (I:Type)(b:I→Barley)(n:Side)(o:Site n)(R:Rep G n)(A C D σ:ℝ),R.path.Bounds R.clip σ A C → G.Simple →2≤ R.p.B → SumBudget (Pointed R b σ) D→∀ (s:Finset I)(l r:ℕ), Splendor (prun R b (sprout o l) (spikes R b s r)) (sprout o (salo R l r)) k (((l+l+1:ℕ)^4:ℕ)* (bankCost R.p.B*(f * (momentPrice u (σ/2)*D)))) E:=by
   obtain ⟨F,⟨hf,A,P,hA,hf'⟩,h⟩:=black G E k hE
   refine ⟨A,P+4,hA,fun I b n o R K C D σ hp hG hB H s l r=> ?_⟩
   let Q:= sprout o l; let V:=flocks R b Q (spikes R b s r); let L:=salo R l r
   let Y(i:Seat n×I):ℝ:= (port R (b i.2))*F (mote R (b i.2)); have hY(i):0 ≤ Y i:=mul_nonneg (ports_n R _) (hf _)
   let P':= bankCost R.p.B*(A*(momentPrice (P+4) (σ/2)*D)); let d:ℝ:= (l+l+1)^ (4:ℕ)
   have ht:= (sparkle (seatP R b) V Y (C:=E) (k:=k) (P:=sprout o L) fun i hi=> ?_); rotate_left
   · have he:= angel R b s o i l r hi; let f':= seatP R b i; let p':=Tar R b i
     refine ⟨ferB R _ _ hp hG,fun U V H=> ferLocal R i.1 (b i.2) hB U V (agrees_mono H he),ferInv R _ _ hp,fun U=> lick R b i _ _ (Turret.incrementA U 0),fun X _ _ W x hv=> h X R W x hv _ _⟩
   refine (ht).up (fun _ h=>h) ?_
   have h₁:∀ y∈Q, SumBudget (fun i=>if y∈Tar R b i then Y i else 0) P':=by
       intro y hy; have hd:= purpose R b D H hp.width (σ/2) (half_pos hp.width) (by linarith only[hp.width]) (P+4)
       have hP: ∀ i:I, (port R (b i)*F (mote R (b i)))*(1+rowL R b i)^4 ≤ A*(Pointed R b (σ-σ/2) i*(1+rowL R b i)^(P+4)):=by
           intro i; let W:ℝ:= rowL R b i
           unfold Pointed; rw [show σ-σ/2=σ/2 by ring]
           have hf: rowAm R b i≤ rowAm R b i*Real.exp (σ/2*W):= le_mul_of_one_le_right (ports_n R _) (Real.one_le_exp (by have h:=hp.width; positivity))
           apply (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hf' _) (ports_n R (b i))) (show 0≤(1+W)^4 by positivity)).trans
           rw [pow_add]; refine le_trans (b:=A*(rowAm R b i*((1+W)^P*(1+W)^ (4:ℕ)))) (le_of_eq ?_) (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hf (by positivity)) (by positivity)); unfold W rowL rowAm; ring
       exact centCost R b y (fun i=>port R (b i)*F (mote R (b i))) (fun i=>mul_nonneg (ports_n R _) (hf _)) (Cost.mono (Cost.scale hd _ (by positivity)) (fun i=>mul_nonneg (mul_nonneg (ports_n R _) (hf _)) (by positivity)) hP)
   let f'(x:Site n)(i:Seat n×I):ℝ:= if x∈Tar R b i then Y i else 0
   have hP:0 ≤ P':= Cost.nonneg (h₁ o (halo_subset _ _ (mem_singleton_self o)))
   apply le_trans (b:=∑ i∈V,∑ x∈Q,f' x i)
   · refine sum_le_sum (fun i hi=>?_); obtain ⟨y,hy,hq⟩:=not_disjoint_iff.mp (mem_filter.mp hi).2
     exact le_trans (le_of_eq (show Y i=f' y i from (if_pos hq).symm)) (single_le_sum (s:=Q) (f:=fun x=> f' x i) (fun x hx=> (h₁ x hx).1 i) hy)
   rw [sum_comm]; apply (sum_le_sum (fun x hx=>Extra.Multi.Budget.cap (h₁ x hx) V)).trans
   rw[sum_const,nsmul_eq_mul]; apply mul_le_mul_of_nonneg_right _ hP; exact_mod_cast (show Q.card ≤ _ from le_trans (Corona.halo_size ..) (by simp))
end YM.Trace.Fen

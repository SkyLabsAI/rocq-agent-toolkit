import { Logo, LogoIcon } from "@/icons/logo/logo";

const Layout = ({ title,children }: { title: string;children: React.ReactNode }) => {

  return (
    <div className="min-h-screen bg-linear-to-b from-[#1B1C1D] to-[#161718]">
        {/* Header */}
        <div className="justify-center border-b border-[#292B2D]">
          <div className="flex items-center gap-4 backdrop-blur-sm  px-10 py-4">
            <div className="flex items-center">

            <LogoIcon  />
            <h1 className="ml-2.5 text-[#E1E2E3] font-['Noto_Sans'] text-base font-normal leading-[normal]">Skylabs AI</h1>
            </div>
            <div className="h-7 w-px mx-4.5 bg-[#292B2D] "></div>
            <h1 className="text-[#97999F] font-['Noto_Sans'] text-base font-normal leading-[normal]">
              {title}
            </h1>
          </div>
        </div>
        
      <div className="mx-auto px-4 sm:px-6 mt-24">
        {children}
      </div>
    </div>
  );
}


export default Layout;
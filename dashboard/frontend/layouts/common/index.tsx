import ThemeSwitcher from "@/components/ThemeSwitcher";
import { Logo, LogoIcon } from "@/icons/logo/logo";

const Layout = ({ title,children }: { title: string;children: React.ReactNode }) => {

  return (
    <div className="min-h-screen bg-elevation-surface text-text flex flex-col">
        {/* Header */}
        <div className="justify-center border-b border-elevation-surface-overlay bg-elevation-surface">
          <div className="flex items-center gap-4 backdrop-blur-sm  px-10 py-4">
            <div className="flex items-center">

            <LogoIcon  />
            <h1 className="ml-2.5 text-[#E1E2E3] font-['Noto_Sans'] text-base font-normal leading-[normal]">Skylabs AI</h1>
            </div>
            <div className="h-7 w-px mx-4.5 bg-[#292B2D] "></div>
            <h1 className="text-[#97999F] font-['Noto_Sans'] text-base font-normal leading-[normal]">
              {title}
            </h1>
            <ThemeSwitcher className="mr-2" />
          </div>              
        </div>
        
      <div className="mx-auto px-4 sm:px-10 mt-24">
        {children}
      </div>
    </div>
  );
}


export default Layout;